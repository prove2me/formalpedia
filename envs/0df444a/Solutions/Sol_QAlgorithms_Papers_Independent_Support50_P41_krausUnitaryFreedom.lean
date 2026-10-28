-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P41.krausUnitaryFreedom
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T00:24:23.439917+00:00
-- url     : https://prove2.me/submissions/38dfea52-a261-451b-8f28-e7ca48ba5e4b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41

-- ===== KFA =====

/-! Generic: two families with equal Gram data are related by a unitary matrix. -/

noncomputable section

namespace X4KF
open scoped Matrix ComplexConjugate InnerProductSpace

variable {P : Type*} [Fintype P]

/-- equal Gram data ⇒ a linear isometry of the whole space sends `β` to `α`. -/
lemma gram_iso {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (α β : P → V) (h : ∀ p q, ⟪β p, β q⟫_ℂ = ⟪α p, α q⟫_ℂ) :
    ∃ T : V →ₗᵢ[ℂ] V, ∀ p, T (β p) = α p := by
  classical
  let F : (P → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ β
  let G : (P → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ α
  have hinner : ∀ c c' : P → ℂ, ⟪F c, F c'⟫_ℂ = ⟪G c, G c'⟫_ℂ := by
    intro c c'
    simp only [F, G, Fintype.linearCombination_apply, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, h]
  have hnorm : ∀ c, ‖G c‖ = ‖F c‖ := by
    intro c
    have h1 := hinner c c
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖F c‖ ^ 2 = ‖G c‖ ^ 2 := by exact_mod_cast h1
    nlinarith [norm_nonneg (F c), norm_nonneg (G c), sq_nonneg (‖F c‖ - ‖G c‖),
      sq_nonneg (‖F c‖ + ‖G c‖)]
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let L0 : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ c, L0 ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [L0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    have : F.quotKerEquivRange.symm ⟨F c, LinearMap.mem_range_self F c⟩ =
        (LinearMap.ker F).mkQ c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  let L : LinearMap.range F →ₗᵢ[ℂ] V :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨x, c, rfl⟩
        change ‖L0 ⟨F c, LinearMap.mem_range_self F c⟩‖ = ‖F c‖
        rw [hL0, hnorm] }
  refine ⟨L.extend, fun p => ?_⟩
  have hb : β p = F (Pi.single p 1) := by
    simp [F, Fintype.linearCombination_apply_single]
  have ha : α p = G (Pi.single p 1) := by
    simp [G, Fintype.linearCombination_apply_single]
  have := LinearIsometry.extend_apply L ⟨F (Pi.single p 1), LinearMap.mem_range_self F _⟩
  rw [hb, ha]
  change L.extend ((⟨F (Pi.single p 1), LinearMap.mem_range_self F _⟩ : LinearMap.range F) : V) = _
  rw [this]
  exact hL0 _

/-- matrix form on `EuclideanSpace ℂ (Fin L)`: equal Gram data ⇒ `α p = U β p` for a unitary `U`. -/
lemma gram_unitary {L : ℕ} [DecidableEq (Fin L)] (α β : P → Fin L → ℂ)
    (h : ∀ p q, ∑ l, conj (β p l) * β q l = ∑ l, conj (α p l) * α q l) :
    ∃ U : Matrix.unitaryGroup (Fin L) ℂ, ∀ p k,
      α p k = ∑ l, (U : Matrix (Fin L) (Fin L) ℂ) k l * β p l := by
  have hin : ∀ x y : Fin L → ℂ, ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin L)), WithLp.toLp 2 y⟫_ℂ =
      ∑ l, conj (x l) * y l := by
    intro x y
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  obtain ⟨T, hT⟩ := gram_iso (V := EuclideanSpace ℂ (Fin L)) (fun p => WithLp.toLp 2 (α p))
    (fun p => WithLp.toLp 2 (β p)) (by
      intro p q
      rw [hin, hin, h])
  let U : Matrix (Fin L) (Fin L) ℂ := fun k l => T (EuclideanSpace.single l 1) k
  have hcol : ∀ l l', ∑ k, conj (U k l) * U k l' = if l = l' then 1 else 0 := by
    intro l l'
    have := T.inner_map_map (EuclideanSpace.single l (1 : ℂ)) (EuclideanSpace.single l' 1)
    have e1 := hin (T (EuclideanSpace.single l (1 : ℂ))).ofLp (T (EuclideanSpace.single l' (1 : ℂ))).ofLp
    simp only [WithLp.toLp_ofLp] at e1
    rw [e1] at this
    simp only [U]
    rw [this, EuclideanSpace.inner_single_left]
    simp [PiLp.single_apply]
  have hU : star U * U = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply]
    exact hcol l l'
  refine ⟨⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, fun p k => ?_⟩
  have hx : (WithLp.toLp 2 (β p) : EuclideanSpace ℂ (Fin L)) =
      ∑ l, β p l • EuclideanSpace.single l (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  have := congrArg (fun v : EuclideanSpace ℂ (Fin L) => v k) (hT p)
  simp only at this
  rw [← this, hx, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, U]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end X4KF

-- ===== KFB =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

lemma sum_pad {d m L : ℕ} {M : Type*} [AddCommMonoid M] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hmL : m ≤ L) (g : Matrix (Fin d) (Fin d) ℂ → M) (hg : g 0 = 0) :
    ∑ k, g (padKraus A L k) = ∑ k, g (A k) := by
  let f : ℕ → M := fun i => if h : i < m then g (A ⟨i, h⟩) else 0
  have h1 : ∑ k : Fin L, g (padKraus A L k) = ∑ i ∈ Finset.range L, f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [padKraus, f]
    split_ifs <;> simp [hg]
  have h2 : ∑ k : Fin m, g (A k) = ∑ i ∈ Finset.range m, f i := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [f]
  rw [h1, h2]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr hmL) fun i _ hi => ?_
  simp only [Finset.mem_range, not_lt] at hi
  simp [f, show ¬ i < m by omega]

lemma kraus_pad {d m L : ℕ} (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hmL : m ≤ L) (X) :
    krausApply (padKraus A L) X = krausApply A X := by
  unfold krausApply
  exact sum_pad A hmL (fun B => B * X * Bᴴ) (by simp)

lemma entry_kraus {d L : ℕ} (A : Fin L → Matrix (Fin d) (Fin d) ℂ) (a i b j : Fin d) :
    krausApply A (Matrix.single j i 1) b a = ∑ l, conj (A l a i) * A l b j := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.single_apply,
    conjTranspose_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single i (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single j (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp [mul_comm]

theorem freedom {d m n : ℕ} (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : OperatorSum Phi A)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) (hB : OperatorSum Phi B) :
    ∃ U : Matrix.unitaryGroup (Fin (max m n)) ℂ,
      ∀ k : Fin (max m n), padKraus A (max m n) k =
        ∑ l, (U : Matrix (Fin (max m n)) (Fin (max m n)) ℂ) k l •
          padKraus B (max m n) l := by
  set L := max m n
  have hAB : ∀ X, krausApply (padKraus A L) X = krausApply (padKraus B L) X := by
    intro X
    rw [kraus_pad A (le_max_left m n), kraus_pad B (le_max_right m n), ← hA.2, ← hB.2]
  obtain ⟨U, hU⟩ := gram_unitary (L := L) (P := Fin d × Fin d)
    (fun p l => padKraus A L l p.1 p.2) (fun p l => padKraus B L l p.1 p.2) (by
      rintro ⟨a, i⟩ ⟨b, j⟩
      simp only
      rw [← entry_kraus, ← entry_kraus, hAB])
  refine ⟨U, fun k => ?_⟩
  ext a i
  rw [hU (a, i) k, Matrix.sum_apply]
  rfl

end X4KF

-- ===== KFSol1 =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem solution {d m n : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d))
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : OperatorSum Phi A)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) (hB : OperatorSum Phi B) :
    ∃ U : Matrix.unitaryGroup (Fin (max m n)) ℂ,
      ∀ k : Fin (max m n), padKraus A (max m n) k =
        ∑ l, (U : Matrix (Fin (max m n)) (Fin (max m n)) ℂ) k l •
          padKraus B (max m n) l :=
  X4KF.freedom Phi A hA B hB

end

#print axioms solution
