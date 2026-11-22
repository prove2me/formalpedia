-- Prove2me | solution 1 for ShiTensor.three_copy_acceptance_operators_are_block_liftings
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T23:25:34.045279+00:00
-- url     : https://prove2.me/submissions/ea77c8ae-5b47-4588-90aa-859a27d09a25

/-
BLIFT-1: the three-copy verifier's acceptance operators ARE single-block liftings of one
operator.

WHAT.  `C3` is the three-copy circuit -- three `ShiEmbed.embedCirc`-embedded copies of
`c : Layered M` on the blocks `castAdd ∘ castAdd`, `castAdd ∘ natAdd`, `natAdd` of
`Fin (M + M + M)`, concatenated (the `C3` of
`ShiTensor.three_copy_conj_projOut_common_eigenvector`, spelled verbatim).  Each of the three
acceptance operators `star (circMatrix C3) * projOut wₖ * circMatrix C3`, at copy `k`'s image
`wₖ` of `out`, equals the block-`k` lifting of the ONE single-copy acceptance operator
`A = star (circMatrix c) * projOut out * circMatrix c`, in the entrywise
`leftBits`/`rightBits` form that
`ShiTensor.conjTranspose_majority_compression_three_blocks` consumes as `P1 P2 P3` (identity
blocks as index-agreement indicators).  ALL THREE blocks are proved.

HOW, AND WHY LOCALITY IS NOT USED.  Nothing accepted connects `circMatrix (embedCirc e he c)`
to a block-extension formula: `isLocal_circMatrix_embedCirc_matrixTower` gives locality only,
and locality cannot say WHICH operator occupies the block.  So the proof evaluates at basis
vectors instead.  A matrix entry is `B y z = Matrix.mulVec B (indicator z) y`; the indicator of
`z : Bits (M + M + M)` factors as the tensor of its three restriction indicators
(`shiBl_ind_tensor`, whose injectivity half `shiBl_bits_ext` comes from
`ShiTensor.tensor_split_append_inverse`); `ShiTensor.runLayered_embed_three_blocks` gives the
action on such a product; `ShiShallow.runLayered_eq_circMatrix_mulVec` converts back.  That
yields something STRONGER than locality, and is the crux: `circMatrix C3` is the threefold
amplitude-array product of `circMatrix c`.  The rest is slotwise algebra -- `projOut wₖ` is
itself a lifting of `projOut out` (`shiBl_projOut_blocks`: the diagonal 0/1 matrix splits
because the three restrictions determine the string), the product is multiplicative
(`shiBl_kron_mul`, one `ShiTensor.sum_split_factor`) and star-compatible, and the two untouched
slots collapse by `star (circMatrix c) * 1 * circMatrix c = 1`, i.e. by
`ShiShallow.circMatrix_unitary` alone.  `mul_star_self_of_star_mul_self` is NOT needed: the
circuit matrix sits on the correct side in every slot.

Built against Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiEmbed_Core
import Theorems.Thm_ShiTensor_runLayered_embed_three_blocks
import Theorems.Thm_ShiTensor_sum_split_factor
import Theorems.Thm_ShiTensor_tensor_split_append_inverse
import Theorems.Thm_ShiShallow_runLayered_eq_circMatrix_mulVec
import Theorems.Thm_ShiShallow_apply1_eq_apply1Matrix_mulVec
import Theorems.Thm_ShiShallow_cnotState_eq_cnotMatrix_mulVec
import Theorems.Thm_ShiShallow_circMatrix_unitary

set_option autoImplicit false

open ShiShallow
open ShiTensor

/-- Amplitude-array tensor product of two operators. -/
private def shiBl_kron {a b : ℕ} (X : Op a) (Y : Op b) : Op (a + b) :=
  Matrix.of fun y z => X (leftBits y) (leftBits z) * Y (rightBits y) (rightBits z)

private lemma shiBl_kron_apply {a b : ℕ} (X : Op a) (Y : Op b) (y z : Bits (a + b)) :
    shiBl_kron X Y y z
      = X (leftBits y) (leftBits z) * Y (rightBits y) (rightBits z) := rfl

/-- Functoriality: the product of two krons is the kron of the products.  The sum over the
middle register splits by `ShiTensor.sum_split_factor`. -/
private lemma shiBl_kron_mul {a b : ℕ} (X X' : Op a) (Y Y' : Op b) :
    shiBl_kron X Y * shiBl_kron X' Y' = shiBl_kron (X * X') (Y * Y') := by
  classical
  ext y u
  have hstep : ∀ z : Bits (a + b),
      shiBl_kron X Y y z * shiBl_kron X' Y' z u
        = (X (leftBits y) (leftBits z) * X' (leftBits z) (leftBits u))
          * (Y (rightBits y) (rightBits z) * Y' (rightBits z) (rightBits u)) := by
    intro z
    first
      | (simp only [shiBl_kron_apply]; ring; done)
      | simp [shiBl_kron_apply, mul_assoc, mul_comm, mul_left_comm]
  calc (shiBl_kron X Y * shiBl_kron X' Y') y u
      = ∑ z : Bits (a + b), shiBl_kron X Y y z * shiBl_kron X' Y' z u := Matrix.mul_apply
    _ = ∑ z : Bits (a + b),
          (X (leftBits y) (leftBits z) * X' (leftBits z) (leftBits u))
            * (Y (rightBits y) (rightBits z) * Y' (rightBits z) (rightBits u)) :=
        Finset.sum_congr rfl fun z _ => hstep z
    _ = (∑ p : Bits a, X (leftBits y) p * X' p (leftBits u))
          * ∑ q : Bits b, Y (rightBits y) q * Y' q (rightBits u) :=
        sum_split_factor (fun p => X (leftBits y) p * X' p (leftBits u))
          (fun q => Y (rightBits y) q * Y' q (rightBits u))
    _ = shiBl_kron (X * X') (Y * Y') y u := by
        first
          | (rw [shiBl_kron_apply, Matrix.mul_apply, Matrix.mul_apply]; done)
          | simp only [shiBl_kron_apply, Matrix.mul_apply]

/-- `star` distributes over the amplitude-array product. -/
private lemma shiBl_star_kron {a b : ℕ} (X : Op a) (Y : Op b) :
    star (shiBl_kron X Y) = shiBl_kron (star X) (star Y) := by
  ext y z
  first
    | (simp only [Matrix.star_apply, shiBl_kron_apply, star_mul']; done)
    | simp [Matrix.star_apply, shiBl_kron_apply, star_mul']

/-- A string on `Bits (M + M + M)` is determined by its three block restrictions: the half of
the three-way splitting bijection that `Def_ShiTensor_Core` deliberately omits. -/
private lemma shiBl_bits_ext {M : ℕ} (u z : Bits (M + M + M))
    (h1 : leftBits (leftBits u) = leftBits (leftBits z))
    (h2 : rightBits (leftBits u) = rightBits (leftBits z))
    (h3 : rightBits u = rightBits z) : u = z := by
  obtain ⟨-, -, hap⟩ := (tensor_split_append_inverse (m := M + M) (p := M))
  obtain ⟨-, -, hap'⟩ := (tensor_split_append_inverse (m := M) (p := M))
  have hl : leftBits u = leftBits z :=
    calc leftBits u
        = Fin.append (leftBits (leftBits u)) (rightBits (leftBits u)) := (hap' (leftBits u)).symm
      _ = Fin.append (leftBits (leftBits z)) (rightBits (leftBits z)) := by rw [h1, h2]
      _ = leftBits z := hap' (leftBits z)
  calc u = Fin.append (leftBits u) (rightBits u) := (hap u).symm
    _ = Fin.append (leftBits z) (rightBits z) := by rw [hl, h3]
    _ = z := hap z

/-- The computational-basis indicator vector. -/
private def shiBl_ind {n : ℕ} (z : Bits n) : QState n := fun u => if u = z then 1 else 0

/-- A matrix entry is recovered by applying the matrix to an indicator. -/
private lemma shiBl_mulVec_ind {n : ℕ} (B : Op n) (y z : Bits n) :
    Matrix.mulVec B (shiBl_ind z) y = B y z := by
  classical
  have h : ∀ u : Bits n, B y u * shiBl_ind z u = if u = z then B y z else 0 := by
    intro u
    by_cases hu : u = z
    · subst hu; simp [shiBl_ind]
    · simp [shiBl_ind, hu]
  calc Matrix.mulVec B (shiBl_ind z) y
      = ∑ u : Bits n, B y u * shiBl_ind z u := Matrix.mulVec_apply_eq_sum B _ y
    _ = ∑ u : Bits n, if u = z then B y z else 0 := Finset.sum_congr rfl fun u _ => h u
    _ = B y z := by simp

/-- The indicator of a three-block string IS the tensor of its three restriction indicators. -/
private lemma shiBl_ind_tensor {M : ℕ} (z : Bits (M + M + M)) :
    shiBl_ind z
      = tensor (tensor (shiBl_ind (leftBits (leftBits z))) (shiBl_ind (rightBits (leftBits z))))
          (shiBl_ind (rightBits z)) := by
  classical
  funext u
  simp only [shiBl_ind, tensor]
  by_cases hu : u = z
  · subst hu
    simp
  · have hne : ¬ (leftBits (leftBits u) = leftBits (leftBits z)
        ∧ rightBits (leftBits u) = rightBits (leftBits z) ∧ rightBits u = rightBits z) :=
      fun hh => hu (shiBl_bits_ext u z hh.1 hh.2.1 hh.2.2)
    by_cases a1 : leftBits (leftBits u) = leftBits (leftBits z)
    · by_cases a2 : rightBits (leftBits u) = rightBits (leftBits z)
      · have a3 : ¬ rightBits u = rightBits z := fun hx => hne ⟨a1, a2, hx⟩
        simp [hu, a3]
      · simp [hu, a2]
    · simp [hu, a1]

/-- The output projector at copy `k`'s image of `out` is the block-`k` lifting of
`projOut out`. -/
private lemma shiBl_projOut_blocks {M : ℕ} (out : Fin M) :
    projOut (Fin.castAdd M (Fin.castAdd M out))
        = shiBl_kron (shiBl_kron (projOut out) (1 : Op M)) (1 : Op M)
      ∧ projOut (Fin.castAdd M (Fin.natAdd M out))
        = shiBl_kron (shiBl_kron (1 : Op M) (projOut out)) (1 : Op M)
      ∧ projOut (Fin.natAdd (M + M) out)
        = shiBl_kron (shiBl_kron (1 : Op M) (1 : Op M)) (projOut out) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  all_goals
    ext y z
    simp only [shiBl_kron_apply, Matrix.one_apply, projOut, Matrix.of_apply]
    by_cases hy : y = z
    · subst hy
      simp [leftBits, rightBits]
    · have hne : ¬ (leftBits (leftBits y) = leftBits (leftBits z)
          ∧ rightBits (leftBits y) = rightBits (leftBits z) ∧ rightBits y = rightBits z) :=
        fun hh => hy (shiBl_bits_ext y z hh.1 hh.2.1 hh.2.2)
      by_cases a1 : leftBits (leftBits y) = leftBits (leftBits z)
      · by_cases a2 : rightBits (leftBits y) = rightBits (leftBits z)
        · have a3 : ¬ rightBits y = rightBits z := fun hx => hne ⟨a1, a2, hx⟩
          simp [hy, a3]
        · simp [hy, a2]
      · simp [hy, a1]

/-- `runLayered` as a matrix action, with the two bridge hypotheses discharged. -/
private lemma shiBl_run {n : ℕ} (c : Layered n) (psi : QState n) :
    runLayered c psi = Matrix.mulVec (circMatrix c) psi :=
  runLayered_eq_circMatrix_mulVec
    (fun U i phi => apply1_eq_apply1Matrix_mulVec U i phi)
    (fun i j hij phi => cnotState_eq_cnotMatrix_mulVec i j hij phi) c psi

/-- **The three-copy verifier's acceptance operators are single-block liftings of one
operator.**  `C3` is the three-copy circuit of
`ShiTensor.three_copy_conj_projOut_common_eigenvector` (same spelling); `A` is the single-copy
acceptance operator; `L1 L2 L3` are pinned by explicit entrywise formulas in
`ShiTensor.leftBits`/`ShiTensor.rightBits`, exactly the `P1 P2 P3` shape of
`ShiTensor.conjTranspose_majority_compression_three_blocks`, an identity block appearing as the
indicator that its two index halves agree.  Unitarity is not hypothesised: it is taken from
`ShiShallow.circMatrix_unitary`, and enters only to collapse the two slots each projector
leaves untouched. -/
theorem solution {M : ℕ} (c : Layered M) (out : Fin M)
    (C3 : Layered (M + M + M))
    (hC3 : C3 =
      ShiEmbed.embedCirc
          ((Fin.castAdd M : Fin (M + M) → Fin (M + M + M)) ∘
            (Fin.castAdd M : Fin M → Fin (M + M)))
          ((Fin.castAdd_injective (M + M) M).comp (Fin.castAdd_injective M M)) c
        ++ ShiEmbed.embedCirc
          ((Fin.castAdd M : Fin (M + M) → Fin (M + M + M)) ∘
            (Fin.natAdd M : Fin M → Fin (M + M)))
          ((Fin.castAdd_injective (M + M) M).comp (Fin.natAdd_injective M M)) c
        ++ ShiEmbed.embedCirc (Fin.natAdd (M + M) : Fin M → Fin (M + M + M))
          (Fin.natAdd_injective M (M + M)) c)
    (A : Op M) (hA : A = star (circMatrix c) * projOut out * circMatrix c)
    (L1 L2 L3 : Op (M + M + M))
    (hL1 : L1 = Matrix.of fun y z =>
      A (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hL2 : L2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * A (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hL3 : L3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * A (rightBits y) (rightBits z)) :
    star (circMatrix C3) * projOut (Fin.castAdd M (Fin.castAdd M out)) * circMatrix C3 = L1
      ∧ star (circMatrix C3) * projOut (Fin.castAdd M (Fin.natAdd M out)) * circMatrix C3 = L2
      ∧ star (circMatrix C3) * projOut (Fin.natAdd (M + M) out) * circMatrix C3 = L3 := by
  classical
  subst hA
  -- The crux, proved entrywise at indicators.
  have hprod : ∀ psi1 psi2 psi3 : QState M,
      Matrix.mulVec (circMatrix C3) (tensor (tensor psi1 psi2) psi3)
        = tensor (tensor (Matrix.mulVec (circMatrix c) psi1)
            (Matrix.mulVec (circMatrix c) psi2)) (Matrix.mulVec (circMatrix c) psi3) := by
    intro psi1 psi2 psi3
    have h1 : runLayered C3 (tensor (tensor psi1 psi2) psi3)
        = tensor (tensor (runLayered c psi1) (runLayered c psi2)) (runLayered c psi3) := by
      rw [hC3]
      exact runLayered_embed_three_blocks c c c psi1 psi2 psi3
    calc Matrix.mulVec (circMatrix C3) (tensor (tensor psi1 psi2) psi3)
        = runLayered C3 (tensor (tensor psi1 psi2) psi3) := (shiBl_run C3 _).symm
      _ = tensor (tensor (runLayered c psi1) (runLayered c psi2)) (runLayered c psi3) := h1
      _ = _ := by rw [shiBl_run c psi1, shiBl_run c psi2, shiBl_run c psi3]
  have hV : circMatrix C3
      = shiBl_kron (shiBl_kron (circMatrix c) (circMatrix c)) (circMatrix c) := by
    ext y z
    calc circMatrix C3 y z
        = Matrix.mulVec (circMatrix C3) (shiBl_ind z) y :=
          (shiBl_mulVec_ind (circMatrix C3) y z).symm
      _ = Matrix.mulVec (circMatrix C3)
            (tensor (tensor (shiBl_ind (leftBits (leftBits z)))
              (shiBl_ind (rightBits (leftBits z)))) (shiBl_ind (rightBits z))) y := by
          rw [shiBl_ind_tensor z]
      _ = tensor (tensor (Matrix.mulVec (circMatrix c) (shiBl_ind (leftBits (leftBits z))))
              (Matrix.mulVec (circMatrix c) (shiBl_ind (rightBits (leftBits z)))))
            (Matrix.mulVec (circMatrix c) (shiBl_ind (rightBits z))) y := by
          rw [hprod]
      _ = shiBl_kron (shiBl_kron (circMatrix c) (circMatrix c)) (circMatrix c) y z := by
          first
            | (simp only [tensor, shiBl_kron_apply, shiBl_mulVec_ind]; done)
            | simp [tensor, shiBl_kron_apply, shiBl_mulVec_ind]
  have hSV : star (circMatrix C3)
      = shiBl_kron (shiBl_kron (star (circMatrix c)) (star (circMatrix c)))
          (star (circMatrix c)) := by
    rw [hV, shiBl_star_kron, shiBl_star_kron]
  have hone : star (circMatrix c) * (1 : Op M) * circMatrix c = (1 : Op M) := by
    rw [mul_one]
    exact circMatrix_unitary c
  have key : ∀ S T U : Op M,
      shiBl_kron (shiBl_kron (star (circMatrix c)) (star (circMatrix c))) (star (circMatrix c))
          * shiBl_kron (shiBl_kron S T) U
          * shiBl_kron (shiBl_kron (circMatrix c) (circMatrix c)) (circMatrix c)
        = shiBl_kron (shiBl_kron (star (circMatrix c) * S * circMatrix c)
            (star (circMatrix c) * T * circMatrix c))
            (star (circMatrix c) * U * circMatrix c) := by
    intro S T U
    simp only [shiBl_kron_mul]
  obtain ⟨q1, q2, q3⟩ := shiBl_projOut_blocks (M := M) out
  refine ⟨?_, ?_, ?_⟩
  all_goals
    first
      | rw [hL1, hSV, hV, q1, key, hone]
      | rw [hL2, hSV, hV, q2, key, hone]
      | rw [hL3, hSV, hV, q3, key, hone]
  all_goals ext y z
  all_goals simp only [shiBl_kron_apply, Matrix.one_apply, Matrix.of_apply]
