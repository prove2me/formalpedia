-- Prove2me | solution 1 for ZigZagStrong.ZigZag.involution_strong_convergence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T11:49:29.450866+00:00
-- url     : https://prove2.me/submissions/ed06ae68-ecce-410e-bb5e-b92fecb4c45e

import Mathlib
import Definitions.Def_BordenaveCollins
import Definitions.Def_StrongConv
import Definitions.Def_DerandSq_permOp
import Definitions.Def_DerandSq_perpCompress
import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_RandomInvolutions
import Theorems.Thm_RandomInvolutions_tendsto_prob_abs_norm_perpOp_sub_ge

section
/-!
# Strong convergence of uniform random involutions: definitions

Shared definitions for the proof of `ZigZagStrong.ZigZag.involution_strong_convergence`.
NEVER EDIT (the Blueprint and all Parts build on this file).

The group is `Γ_r = Z₂^{*r}`, in the encoding `BordenaveCollins.G 0 r` (no free generators, `r`
involutions `m_i = genL (Sum.inr i)`), so that the published Bordenave–Collins statements
(`exists_linearization`, `norm_sum_cfun_mul_trace_Bprod_le`, `tendsto_expFix`,
`tendsto_re_trTau_pow_rpow`) apply verbatim with `r := 0`, `s := r`.

* `homI τ : G 0 r →* Perm (Fin N)` for a tuple of involutions `τ`.
* The conditional model `OmK r N κ`: the `i`-th involution has exactly `κ i` fixed points;
  admissible sizes `AdmK N κ` (`κ i ≤ N`, `κ i ≡ N mod 2`), the filter `admF κ` of admissible
  sizes, the weight `lam κ = 1 + ∑ κ i`.
* Expected fixed points `expFixOn`, `expFixK`; the compressed model operator `perpOp`; the
  spectral functional `specE` of any finite family of representations.
* Colourings with loops of the closed path of a word, and their weights `wtF`, `wtK`.
* The coefficient counts `Bcount` (conjugates of `m_i`) and `C2count` (the two-loop shapes
  `a (ρ m_j ρ⁻¹ σ m_i σ⁻¹)^t a⁻¹`).
* `toAlg`: a scalar `*`-polynomial as an element of the group algebra.
-/

open Finset BordenaveCollins

noncomputable section

namespace RandomInvolutions.Dev

/-! ## The group `Γ_r = G 0 r` and its words -/

/-- The inverse letter. -/
def bar {r s : ℕ} : Lt r s → Lt r s
  | Sum.inl (i, b) => Sum.inl (i, !b)
  | Sum.inr j => Sum.inr j

/-- A reduced word: no letter is followed by its inverse. -/
def Red {r s : ℕ} (u : List (Lt r s)) : Prop := u.IsChain (fun a b => b ≠ bar a)

/-! ## Involutions and the representation they define -/

/-! ## The conditional model `M(N, κ)` -/

/-! ## Expected fixed points -/

/-! ## Operators -/

/-! ## Colourings with loops of the closed path of a word

A path is `x : Fin (u.length + 1) → α` with `x t = letter_t (x (t+1))` (so that
`x t = wordPermI τ (u.drop t) y`). Step `t` with letter `m_i` is a *loop* of colour `i` at
`x t` when `x t = x (t+1)` (that vertex is fixed by `τ_i`), and a *pair* `{x t, x (t+1)}` of
`τ_i` otherwise. -/

/-! ## The coefficient counts -/

/-! ## Scalar polynomials as group-algebra elements -/

/-- The group element of a letter `s_i` (`Sum.inl i`) or `s_i*` (`Sum.inr i`): `m_i` and
`m_i⁻¹ = m_i`. -/
def letterG {r : ℕ} : Fin r ⊕ Fin r → G 0 r
  | Sum.inl i => mI i
  | Sum.inr i => (mI i)⁻¹

/-- The group element of a word. -/
def wordG {r : ℕ} (w : FreeMonoid (Fin r ⊕ Fin r)) : G 0 r := (w.toList.map letterG).prod

/-- A polynomial as an element of the matrix-coefficient group algebra. -/
def toAlg {D r : ℕ} (P : StrongConv.NCPoly D r) : MG D 0 r :=
  P.sum fun w A => MonoidAlgebra.single (wordG w) A

end RandomInvolutions.Dev

end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-!
# Part X: mixing over the fixed-point counts

* `mixture`: the uniform law on tuples of involutions is the mixture of the conditional models.
* `fixCount_exp_le`: `E[#fix] ≤ √N + 1`. In fact `E[#fix²] = N` exactly (`sum_fix_sq`): multiplying
  by the transposition `(x y)` is a bijection between involutions fixing `x ≠ y` and involutions
  swapping them, so `E[f (f - 1)] = E[N - f]`; then Cauchy–Schwarz gives `E[#fix] ≤ √N`.
* `mix_affine`: a conditional bound `a * lam κ + b` integrates to `a (1 + r (√N + 1)) + b`.
* `expFix_unif_le`, `upper_unif`.
-/
abbrev Inv (N : ℕ) := ZigZagStrong.ZigZag.Involution N

/-! ## Generic finite probability -/

/-! ## The mixture -/

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev.PartX
variable {r : ℕ}
/-! ## The second moment of the number of fixed points -/

instance (N : ℕ) : Nonempty (Inv N) := ⟨⟨1, fun _ => rfl⟩⟩

end RandomInvolutions.Dev.PartX
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part T2: the core theorem -/
theorem tendsto_prob_abs_norm_perpOp_sub_ge {D : ℕ} (x : MG D 0 r) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => StrongConv.uniformProb
      (fun τ : Fin r → ZigZagStrong.ZigZag.Involution N =>
        ε ≤ |‖perpOp (homI τ) x‖ - ‖regOp x‖|)) atTop (𝓝 0) := by
  exact RandomInvolutions.tendsto_prob_abs_norm_perpOp_sub_ge x ε hε

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
/-!
# Part B: the bridge to the ZigZag encoding

`bridge_model`: for a scalar polynomial `P`, `P` evaluated at the compressed permutation
operators has the same norm as `perpOp (homI τ) (toAlg P)`.
`bridge_limit`: `P` evaluated at `regularL2` of the generators of `FreeInvolutions r` has the same
norm as `regOp (toAlg P)` (on `ℓ²(F_0 * Γ_r)`).
(Ported from `Solutions/ZZB/Bridge.lean`.)
-/
/-- Conjugation by a unitary. -/
def cj (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : F →L[ℂ] F :=
  (W : E →L[ℂ] F).comp (T.comp (W.symm : F →L[ℂ] E))

theorem cj_apply (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (x : F) : cj W T x = W (T (W.symm x)) := rfl

theorem cj_mul (W : E ≃ₗᵢ[ℂ] F) (S T : E →L[ℂ] E) : cj W (S * T) = cj W S * cj W T := by
  ext x; simp [cj_apply]

theorem cj_one (W : E ≃ₗᵢ[ℂ] F) : cj W 1 = 1 := by
  ext x; simp [cj_apply]

theorem cj_zero (W : E ≃ₗᵢ[ℂ] F) : cj W 0 = 0 := by
  ext x; simp [cj_apply]

theorem cj_add (W : E ≃ₗᵢ[ℂ] F) (S T : E →L[ℂ] E) : cj W (S + T) = cj W S + cj W T := by
  ext x; simp [cj_apply]

theorem cj_smul (W : E ≃ₗᵢ[ℂ] F) (c : ℂ) (T : E →L[ℂ] E) : cj W (c • T) = c • cj W T := by
  ext x; simp [cj_apply]

theorem cj_sum {α : Type*} (W : E ≃ₗᵢ[ℂ] F) (s : Finset α) (T : α → E →L[ℂ] E) :
    cj W (∑ a ∈ s, T a) = ∑ a ∈ s, cj W (T a) := by
  induction s using Finset.induction_on with
  | empty => ext x; simp [cj_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cj_add, ih]

theorem cj_star (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : cj W (star T) = star (cj W T) := by
  simp only [cj, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]
  rfl

theorem cj_list_prod (W : E ≃ₗᵢ[ℂ] F) (l : List (E →L[ℂ] E)) :
    cj W l.prod = (l.map (cj W)).prod := by
  induction l with
  | nil => exact cj_one W
  | cons a l ih => rw [List.prod_cons, cj_mul, ih, List.map_cons, List.prod_cons]

theorem norm_cj (W : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : ‖cj W T‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [cj_apply, LinearIsometryEquiv.norm_map]
    calc ‖T (W.symm x)‖ ≤ ‖T‖ * ‖W.symm x‖ := T.le_opNorm _
      _ = ‖T‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    have : T x = W.symm (cj W T (W x)) := by simp [cj_apply]
    rw [this, LinearIsometryEquiv.norm_map]
    calc ‖cj W T (W x)‖ ≤ ‖cj W T‖ * ‖W x‖ := (cj W T).le_opNorm _
      _ = ‖cj W T‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

end RandomInvolutions.Dev.PartB
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- One copy of `H`. -/
def e1 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    H ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Fin 1 => H) where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => H)).symm.toLinearEquiv
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2]
    simp [PiLp.equivOfUnique]

theorem e1_symm_apply (x : PiLp 2 (fun _ : Fin 1 => H)) : (e1 H).symm x = x 0 := rfl

theorem e1_apply (x : H) (i : Fin 1) : e1 H x i = x := by
  fin_cases i; rfl

theorem tensorOp_one (A : Matrix (Fin 1) (Fin 1) ℂ) (T : H →L[ℂ] H) :
    AccessibleMaps.tensorOp A T = cj (e1 H) (A 0 0 • T) := by
  ext x i
  fin_cases i
  simp [AccessibleMaps.tensorOp, AccessibleMaps.inject, cj_apply, e1_apply, e1_symm_apply]

theorem tensorOp_one' (A : Matrix (Fin 1) (Fin 1) ℂ) (T : H →L[ℂ] H) :
    StrongConv.tensorOp A T = cj (e1 H) (A 0 0 • T) := by
  ext x i
  fin_cases i
  simp [StrongConv.tensorOp, cj_apply, e1_apply, e1_symm_apply]

/-- A scalar polynomial (the `(0,0)` entries) evaluated at a tuple. -/
def scal {r : ℕ} (P : StrongConv.NCPoly 1 r) (u : Fin r → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ w ∈ P.support, (P w 0 0) • StrongConv.wordOp u w

theorem seval_eq {r : ℕ} (P : StrongConv.NCPoly 1 r) (u : Fin r → H →L[ℂ] H) :
    StrongConv.NCPoly.eval P u = cj (e1 H) (scal P u) := by
  rw [StrongConv.NCPoly.eval, scal, cj_sum]
  exact Finset.sum_congr rfl fun w _ => tensorOp_one' _ _

theorem norm_seval {r : ℕ} (P : StrongConv.NCPoly 1 r) (u : Fin r → H →L[ℂ] H) :
    ‖StrongConv.NCPoly.eval P u‖ = ‖scal P u‖ := by
  rw [seval_eq, norm_cj]

theorem wordOp_intertwine {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {r : ℕ} (u : Fin r → H →L[ℂ] H) (v : Fin r → F →L[ℂ] F) (K : F →L[ℂ] H)
    (h1 : ∀ i, (u i).comp K = K.comp (v i))
    (h2 : ∀ i, (star (u i)).comp K = K.comp (star (v i))) (w : FreeMonoid (Fin r ⊕ Fin r)) :
    (StrongConv.wordOp u w).comp K = K.comp (StrongConv.wordOp v w) := by
  unfold StrongConv.wordOp
  induction w.toList with
  | nil => ext x; simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    have ha : (StrongConv.letterOp u a).comp K = K.comp (StrongConv.letterOp v a) := by
      cases a with
      | inl i => exact h1 i
      | inr i => exact h2 i
    change (StrongConv.letterOp u a).comp ((List.map (StrongConv.letterOp u) l).prod.comp K) =
      K.comp ((StrongConv.letterOp v a).comp (List.map (StrongConv.letterOp v) l).prod)
    rw [ih, ← ContinuousLinearMap.comp_assoc, ha, ContinuousLinearMap.comp_assoc]

theorem scal_intertwine {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {r : ℕ} (P : StrongConv.NCPoly 1 r) (u : Fin r → H →L[ℂ] H)
    (v : Fin r → F →L[ℂ] F) (K : F →L[ℂ] H)
    (h1 : ∀ i, (u i).comp K = K.comp (v i))
    (h2 : ∀ i, (star (u i)).comp K = K.comp (star (v i))) :
    (scal P u).comp K = K.comp (scal P v) := by
  ext x
  simp only [scal, ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  exact congrArg (fun T : F →L[ℂ] H => T x) (wordOp_intertwine u v K h1 h2 w)

theorem scal_cj {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {r : ℕ} (P : StrongConv.NCPoly 1 r) (v : Fin r → H →L[ℂ] H)
    (W : H ≃ₗᵢ[ℂ] F) : scal P (fun i => cj W (v i)) = cj W (scal P v) := by
  rw [scal, scal, cj_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [cj_smul, StrongConv.wordOp, StrongConv.wordOp, cj_list_prod, List.map_map]
  congr 3
  funext l
  cases l with
  | inl i => rfl
  | inr i => exact (cj_star W (v i)).symm

end RandomInvolutions.Dev.PartB
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
variable {r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ## `opOf` of `toAlg P` for a scalar polynomial -/
theorem opOf_eq_sum (π : G 0 r → H →L[ℂ] H) (x : MG 1 0 r) :
    opOf π x = x.coeff.sum fun g A => AccessibleMaps.tensorOp A (π g) := rfl

theorem tensorOp_zero_left (T : H →L[ℂ] H) :
    AccessibleMaps.tensorOp (0 : Matrix (Fin 1) (Fin 1) ℂ) T = 0 := by
  rw [tensorOp_one]; simp [cj_zero]

theorem tensorOp_add_left (A B : Matrix (Fin 1) (Fin 1) ℂ) (T : H →L[ℂ] H) :
    AccessibleMaps.tensorOp (A + B) T =
      AccessibleMaps.tensorOp A T + AccessibleMaps.tensorOp B T := by
  rw [tensorOp_one, tensorOp_one, tensorOp_one, Matrix.add_apply, add_smul, cj_add]

theorem opOf_zero (π : G 0 r → H →L[ℂ] H) : opOf π (0 : MG 1 0 r) = 0 := by
  simp [opOf]

theorem opOf_add' (π : G 0 r → H →L[ℂ] H) (x y : MG 1 0 r) :
    opOf π (x + y) = opOf π x + opOf π y := by
  rw [opOf_eq_sum, opOf_eq_sum, opOf_eq_sum, MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun g => tensorOp_zero_left (π g))
    (fun g A B => tensorOp_add_left A B (π g))

theorem opOf_single (π : G 0 r → H →L[ℂ] H) (g : G 0 r) (A : Matrix (Fin 1) (Fin 1) ℂ) :
    opOf π (MonoidAlgebra.single g A) = AccessibleMaps.tensorOp A (π g) := by
  rw [opOf_eq_sum, MonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (tensorOp_zero_left (π g))

/-- `opOf π` as an additive map. -/
def opHom (π : G 0 r → H →L[ℂ] H) : MG 1 0 r →+
    (PiLp 2 (fun _ : Fin 1 => H) →L[ℂ] PiLp 2 (fun _ : Fin 1 => H)) where
  toFun := opOf π
  map_zero' := opOf_zero π
  map_add' := opOf_add' π

theorem wordOp_eq (π : G 0 r →* (H →L[ℂ] H)) (hstar : ∀ i, star (π (mI i)) = π (mI i)⁻¹)
    (w : FreeMonoid (Fin r ⊕ Fin r)) :
    StrongConv.wordOp (fun i => π (mI i)) w = π (wordG w) := by
  unfold StrongConv.wordOp wordG
  rw [map_list_prod, List.map_map]
  congr 2
  funext l
  cases l with
  | inl i => rfl
  | inr i => exact hstar i

theorem opOf_toAlg (π : G 0 r →* (H →L[ℂ] H)) (hstar : ∀ i, star (π (mI i)) = π (mI i)⁻¹)
    (P : StrongConv.NCPoly 1 r) :
    opOf (fun g => π g) (toAlg P) = cj (e1 H) (scal P (fun i => π (mI i))) := by
  have h1 : opOf (fun g => π g) (toAlg P) =
      ∑ w ∈ P.support, opOf (fun g => π g) (MonoidAlgebra.single (wordG w) (P w)) := by
    change opHom (fun g => π g) (toAlg P) = _
    rw [toAlg, Finsupp.sum, map_sum]
    rfl
  rw [h1, scal, cj_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [opOf_single, tensorOp_one, wordOp_eq π hstar]

end RandomInvolutions.Dev.PartB
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
open DerandSq
/-! ## The model side -/
theorem permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N))
    (j : Fin N) : permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

theorem permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply]
  rfl

theorem permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

theorem inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    inner ℂ (permOp π x) y = inner ℂ x (permOp π⁻¹ y) := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem star_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) : star (permOp π) = permOp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_permOp, inv_inv]

/-- A permutation representation as a monoid homomorphism into operators. -/
def permHom {M : Type*} [Monoid M] {N : ℕ} (π : M →* Equiv.Perm (Fin N)) :
    M →* (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) where
  toFun g := permOp (π g)
  map_one' := by rw [map_one, permOp_one]
  map_mul' g h := by rw [map_mul, permOp_mul]

/-- `1 - J` on `ℂ^N`. -/
def Qn (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ)))

theorem Qn_apply {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    Qn N x i = x i - (N : ℂ)⁻¹ * ∑ j, x j := by
  show (Matrix.toEuclideanCLM (𝕜 := ℂ)
    (1 - (N : ℂ)⁻¹ • Matrix.of (fun _ _ : Fin N => (1 : ℂ))) x).ofLp i = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib,
    Matrix.one_apply]

theorem inner_ones {N : ℕ} (y : EuclideanSpace ℂ (Fin N)) :
    ⟪StrongConv.onesVec N, y⟫_ℂ = ∑ j, y j := by
  simp [StrongConv.onesVec, PiLp.inner_apply]

theorem sum_Qn {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : ∑ j, Qn N x j = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Qn_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem Qn_mem {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : Qn N x ∈ StrongConv.OnesPerp N := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_ones, sum_Qn]

theorem Qn_of_mem {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) (hx : x ∈ StrongConv.OnesPerp N) :
    Qn N x = x := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_ones] at hx
  ext i
  rw [Qn_apply, hx, mul_zero, sub_zero]

theorem sub_Qn {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) :
    x - Qn N x = ((N : ℂ)⁻¹ * ∑ j, x j) • StrongConv.onesVec N := by
  ext i
  simp [Qn_apply, StrongConv.onesVec]

theorem norm_Qn_le {N : ℕ} (x : EuclideanSpace ℂ (Fin N)) : ‖Qn N x‖ ≤ ‖x‖ := by
  have horth : ⟪Qn N x, x - Qn N x⟫_ℂ = 0 := by
    rw [sub_Qn, inner_smul_right, ← inner_conj_symm, inner_ones, sum_Qn]
    simp
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [add_sub_cancel] at h
  have : ‖Qn N x‖ * ‖Qn N x‖ ≤ ‖x‖ * ‖x‖ := by
    rw [h]; nlinarith [mul_self_nonneg ‖x - Qn N x‖]
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this

/-- The projection onto `1^⊥`, as a map into the subspace. -/
def proj (N : ℕ) : EuclideanSpace ℂ (Fin N) →L[ℂ] StrongConv.OnesPerp N :=
  (Qn N).codRestrict _ Qn_mem

theorem incl_proj (N : ℕ) : (StrongConv.OnesPerp N).subtypeL.comp (proj N) = Qn N := by
  ext x; rfl

theorem proj_incl (N : ℕ) :
    (proj N).comp (StrongConv.OnesPerp N).subtypeL = ContinuousLinearMap.id ℂ _ := by
  ext x : 1
  exact Subtype.ext (Qn_of_mem x.1 x.2)

theorem norm_proj_le (N : ℕ) : ‖proj N‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_Qn_le x

theorem norm_incl_le (N : ℕ) : ‖(StrongConv.OnesPerp N).subtypeL‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp

theorem permOp_incl {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (DerandSq.permOp σ).comp (StrongConv.OnesPerp N).subtypeL =
      (StrongConv.OnesPerp N).subtypeL.comp (StrongConv.permOpPerp σ) := by
  ext x; rfl

theorem star_permOpPerp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    star (StrongConv.permOpPerp σ) = StrongConv.permOpPerp σ⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change ⟪DerandSq.permOp σ⁻¹ x, (y : EuclideanSpace ℂ (Fin N))⟫_ℂ =
    ⟪(x : EuclideanSpace ℂ (Fin N)), DerandSq.permOp σ y⟫_ℂ
  rw [← star_permOp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]

theorem norm_perpCompress {r N : ℕ} (P : StrongConv.NCPoly 1 r)
    (σ : Fin r → Equiv.Perm (Fin N)) :
    ‖DerandSq.perpCompress 1 N (cj (e1 _) (scal P (fun i => DerandSq.permOp (σ i))))‖ =
      ‖scal P (fun i => StrongConv.permOpPerp (σ i))‖ := by
  set K := (StrongConv.OnesPerp N).subtypeL
  set S := scal P (fun i => DerandSq.permOp (σ i))
  set S' := scal P (fun i => StrongConv.permOpPerp (σ i))
  have hS : S.comp K = K.comp S' := scal_intertwine P _ _ K (fun i => permOp_incl (σ i))
    (fun i => by rw [star_permOp, star_permOpPerp]; exact permOp_incl _)
  have hpc : DerandSq.perpCompress 1 N (cj (e1 _) S)
      = cj (e1 _) (K.comp (S'.comp (proj N))) := by
    rw [DerandSq.perpCompress]
    simp only [tensorOp_one, Matrix.one_apply_eq, one_smul]
    change cj _ (Qn N) * (cj _ S * cj _ (Qn N)) = _
    rw [← cj_mul, ← cj_mul]
    congr 1
    rw [← incl_proj]
    ext x : 1
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    have h1 := congrArg (fun T => T (proj N x)) hS
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun T => T (S' (proj N x))) (proj_incl N)
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [h2]
    rfl
  rw [hpc, norm_cj]
  apply le_antisymm
  · calc ‖K.comp (S'.comp (proj N))‖ ≤ ‖K‖ * (‖S'‖ * ‖proj N‖) :=
          (K.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (S'.opNorm_comp_le _)
            (norm_nonneg _))
      _ ≤ 1 * (‖S'‖ * 1) := by
          gcongr
          · exact norm_incl_le N
          · exact norm_proj_le N
      _ = ‖S'‖ := by ring
  · have : S' = (proj N).comp ((K.comp (S'.comp (proj N))).comp K) := by
      ext x : 1
      simp only [ContinuousLinearMap.comp_apply]
      have h2 := congrArg (fun T => T (S' (proj N (K x)))) (proj_incl N)
      have h3 := congrArg (fun T => T x) (proj_incl N)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h2 h3
      rw [h2, h3]
    calc ‖S'‖ = ‖(proj N).comp ((K.comp (S'.comp (proj N))).comp K)‖ := by rw [← this]
      _ ≤ ‖proj N‖ * (‖K.comp (S'.comp (proj N))‖ * ‖K‖) :=
          ((proj N).opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖K.comp (S'.comp (proj N))‖ * 1) := by
          gcongr
          · exact norm_proj_le N
          · exact norm_incl_le N
      _ = _ := by ring

theorem homI_mI {r N : ℕ} (τ : Fin r → ZigZagStrong.ZigZag.Involution N) (i : Fin r) :
    homI τ (mI i) = (τ i).1 := by
  simp [homI, mI, DerandSq.mGen, invHomI, ZMod.val_one]

end RandomInvolutions.Dev.PartB
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
variable {r : ℕ}
theorem bridge_model {N : ℕ} (hN : 1 ≤ N) (P : StrongConv.NCPoly 1 r)
    (τ : Fin r → ZigZagStrong.ZigZag.Involution N) :
    ‖P.eval (fun i => StrongConv.permOpPerp (τ i).val)‖ = ‖perpOp (homI τ) (toAlg P)‖ := by
  rw [norm_seval, ← norm_perpCompress, perpOp]
  have h := opOf_toAlg (permHom (homI τ))
    (fun i => by
      change star (DerandSq.permOp _) = DerandSq.permOp _
      rw [star_permOp]
      exact congrArg DerandSq.permOp (map_inv (homI τ) (mI i)).symm) P
  have hu : (fun i => permHom (homI τ) (mI i)) = fun i => DerandSq.permOp (τ i).1 :=
    funext fun i => by
      change DerandSq.permOp (homI τ (mI i)) = _
      rw [homI_mI]
  rw [hu] at h
  rw [← h]
  rfl

end RandomInvolutions.Dev.PartB
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
/-! ## Part B: the bridge to the ZigZag encoding -/
alias bridge_model := RandomInvolutions.Dev.PartB.bridge_model

end RandomInvolutions.Dev
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
variable {r : ℕ}
open ZigZagStrong.ZigZag
/-! ## The limit side -/
theorem leftReg_apply {Γ : Type*} [Group Γ] (g : Γ) (f : L2 Γ) (h : Γ) :
    DerandSq.leftReg g f h = f (g⁻¹ * h) := rfl

theorem leftReg_mul {Γ : Type*} [Group Γ] (g h : Γ) :
    DerandSq.leftReg (g * h) = DerandSq.leftReg g * DerandSq.leftReg h := by
  ext f k
  simp [leftReg_apply, mul_assoc]

theorem leftReg_one {Γ : Type*} [Group Γ] : DerandSq.leftReg (1 : Γ) = 1 := by
  ext f k
  simp [leftReg_apply]

/-- The left regular representation as a monoid homomorphism into operators. -/
def regHom (Γ : Type*) [Group Γ] : Γ →* (L2 Γ →L[ℂ] L2 Γ) where
  toFun g := DerandSq.leftReg g
  map_one' := leftReg_one
  map_mul' := leftReg_mul

theorem star_leftReg {Γ : Type*} [Group Γ] (g : Γ) :
    star (DerandSq.leftReg g) = DerandSq.leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have := (Equiv.mulLeft g).tsum_eq (fun h => inner ℂ (x h) (DerandSq.leftReg g y h))
  rw [← this]
  refine tsum_congr fun h => ?_
  simp [leftReg_apply]

/-- Transport of `ℓ²` along a bijection. -/
def lpMap {A B : Type*} (e : A ≃ B) : L2 A →ₗ[ℂ] L2 B where
  toFun f := ⟨fun y => f (e.symm y), by
    have hf := lp.memℓp f
    rw [memℓp_gen_iff (by norm_num)] at hf
    change Memℓp (fun y : B => f (e.symm y)) 2
    rw [memℓp_gen_iff (by norm_num)]
    exact e.symm.summable_iff.mpr hf⟩
  map_add' f g := by ext y; rfl
  map_smul' c f := by ext y; rfl

theorem lpMap_apply {A B : Type*} (e : A ≃ B) (f : L2 A) (y : B) : lpMap e f y = f (e.symm y) :=
  rfl

/-- The unitary `ℓ²(A) ≃ ℓ²(B)` induced by a bijection. -/
def lpCongr {A B : Type*} (e : A ≃ B) : L2 A ≃ₗᵢ[ℂ] L2 B where
  toLinearEquiv :=
    { lpMap e with
      invFun := lpMap e.symm
      left_inv := fun f => by ext x; simp [lpMap_apply]
      right_inv := fun f => by ext x; simp [lpMap_apply] }
  norm_map' f := by
    change ‖lpMap e f‖ = ‖f‖
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun x => ‖f x‖ ^ (2 : ENNReal).toReal)

theorem lpCongr_apply {A B : Type*} (e : A ≃ B) (f : L2 A) (y : B) :
    lpCongr e f y = f (e.symm y) := rfl

theorem lpCongr_symm_apply {A B : Type*} (e : A ≃ B) (f : L2 B) (x : A) :
    (lpCongr e).symm f x = f (e x) := by
  change f (e.symm.symm x) = _
  rfl

end RandomInvolutions.Dev.PartB
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
variable {r : ℕ}
open ZigZagStrong.ZigZag
variable {Γ : Type*} [Group Γ]
/-- `F_0 ∗ G → G`. -/
def collapse (Γ : Type*) [Group Γ] : Monoid.Coprod (FreeGroup (Fin 0)) Γ →* Γ :=
  Monoid.Coprod.lift 1 (MonoidHom.id Γ)

theorem inr_collapse (x : Monoid.Coprod (FreeGroup (Fin 0)) Γ) :
    Monoid.Coprod.inr (collapse Γ x) = x := by
  have h : (Monoid.Coprod.inr : Γ →* Monoid.Coprod (FreeGroup (Fin 0)) Γ).comp (collapse Γ) =
      MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · apply FreeGroup.ext_hom
      intro a
      exact a.elim0
    · ext g
      simp [collapse]
  exact congrArg (fun f => f x) h

theorem collapse_inr (g : Γ) : collapse Γ (Monoid.Coprod.inr g) = g := by
  simp [collapse]

/-- `F_0 ∗ G ≃ G` as types. -/
def collapseEquiv (Γ : Type*) [Group Γ] : Monoid.Coprod (FreeGroup (Fin 0)) Γ ≃ Γ where
  toFun := collapse Γ
  invFun := Monoid.Coprod.inr
  left_inv := inr_collapse
  right_inv := collapse_inr

theorem cj_leftReg (g : Γ) :
    cj (lpCongr (collapseEquiv Γ)) (DerandSq.leftReg (Monoid.Coprod.inr g)) = regularL2 g := by
  ext f y
  rw [cj_apply, lpCongr_apply]
  change ((lpCongr (collapseEquiv Γ)).symm f) ((Monoid.Coprod.inr g)⁻¹ *
    (collapseEquiv Γ).symm y) = f ((Equiv.mulLeft g).symm y)
  rw [lpCongr_symm_apply]
  change f (collapse Γ ((Monoid.Coprod.inr g)⁻¹ * Monoid.Coprod.inr y)) = f (g⁻¹ * y)
  rw [map_mul, map_inv, collapse_inr, collapse_inr]

theorem norm_scal_limit (P : StrongConv.NCPoly 1 r) :
    ‖scal P (fun j => DerandSq.leftReg (mI j : G 0 r))‖ =
      ‖scal P (fun j => regularL2 (involutionGenerator j))‖ := by
  rw [← norm_cj (lpCongr (collapseEquiv (DerandSq.Gam r))), ← scal_cj]
  have h : (fun j => cj (lpCongr (collapseEquiv (DerandSq.Gam r)))
      (DerandSq.leftReg (mI j : G 0 r))) =
      fun j => regularL2 (involutionGenerator j) := funext fun j => cj_leftReg _
  rw [h]

end RandomInvolutions.Dev.PartB
end
end

section
open Finset BordenaveCollins
open scoped Classical InnerProductSpace
set_option linter.unusedSectionVars false
noncomputable section
namespace RandomInvolutions.Dev.PartB
variable {r : ℕ}
theorem bridge_limit (P : StrongConv.NCPoly 1 r) :
    ‖P.eval (fun i => ZigZagStrong.ZigZag.regularL2 (ZigZagStrong.ZigZag.involutionGenerator i))‖ =
      ‖regOp (toAlg P)‖ := by
  rw [norm_seval, ← norm_scal_limit]
  have h := opOf_toAlg (regHom (G 0 r)) (fun i => star_leftReg (mI i)) P
  have h' : regOp (toAlg P) = cj (e1 _) (scal P (fun j => DerandSq.leftReg (mI j : G 0 r))) := h
  rw [h', norm_cj]

end RandomInvolutions.Dev.PartB
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
alias bridge_limit := RandomInvolutions.Dev.PartB.bridge_limit

/-! ## Glue (proved here) -/
theorem uniformProb_nonneg {Ω : Type*} [Fintype Ω] (A : Ω → Prop) :
    0 ≤ StrongConv.uniformProb A := by
  unfold StrongConv.uniformProb
  positivity

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
noncomputable section
namespace RandomInvolutions.Dev
variable {r : ℕ}
theorem uniformProb_mono {Ω : Type*} [Fintype Ω] (A B : Ω → Prop) (h : ∀ ω, A ω → B ω) :
    StrongConv.uniformProb A ≤ StrongConv.uniformProb B := by
  unfold StrongConv.uniformProb
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card fun ω hω => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω

end RandomInvolutions.Dev
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology
theorem involution_strong_convergence_dev (r : ℕ) :
    StrongConvergence (fun n => finiteLaw (Ω := Fin r → Involution (n+2)))
      (fun _ τ i => StrongConv.permOpPerp (τ i).val)
      (fun i => regularL2 (involutionGenerator i)) := by
  intro P ε hε
  have h := (RandomInvolutions.Dev.tendsto_prob_abs_norm_perpOp_sub_ge (RandomInvolutions.Dev.toAlg P) ε hε).comp (tendsto_add_atTop_nat 2)
  refine squeeze_zero (fun n => ?_) (fun n => ?_) h
  · exact RandomInvolutions.Dev.uniformProb_nonneg _
  · simp only [Function.comp_apply]
    apply RandomInvolutions.Dev.uniformProb_mono
    intro τ hτ
    simp only [Set.mem_ofPred_eq] at hτ
    rw [RandomInvolutions.Dev.bridge_model (by omega) P τ, RandomInvolutions.Dev.bridge_limit P] at hτ
    exact hτ.le

end ZigZagStrong.ZigZag
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-!
# Part F, toolkit: normal forms in `F_r * Γ_s` (van der Waerden's trick) and reduced words

Stated for `G r s`, `Lt r s` with the `RandomInvolutions.Dev` versions of `bar`, `Red`, `CycRed`; Part F uses it at
`G 0 r`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

end RandomInvolutions.Dev.PartF
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartF
variable {r s : ℕ}
/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

end RandomInvolutions.Dev.PartF
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3a.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

end RandomInvolutions.Dev.PartP3a.F1
end
end

section
open Finset
noncomputable section
namespace RandomInvolutions.Dev.PartP3b.F1
open BordenaveCollins RandomInvolutions RandomInvolutions.Dev
variable {r s : ℕ}
/-!
# Part P3a, module 0: normal forms in `F_r * Γ_s` (van der Waerden's trick)

Copy of bc214's Part F1 (general `G r s`), so that the first-passage modules below do not depend
on the Part F stubs.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## The stubs -/

end RandomInvolutions.Dev.PartP3b.F1
end
end

section
open Finset BordenaveCollins
noncomputable section
namespace RandomInvolutions.Dev.PartW
variable {r s : ℕ}
/-!
# Part W, words: the two-loop factorizations of a cyclically reduced word and `C2count`

The first half is the reduced-word toolkit of Part F (normal forms by van der Waerden's trick),
copied here because Parts do not import each other.  The second half identifies the folds
`Par u j i` with the tuples counted by `C2count i j (a * wprod u * a⁻¹)`.
-/
/-! ## Group lemmas for `G r s`

(`rw`/`simp` with the generic group lemmas fail on `G r s` because of an instance diamond in
`Monoid.Coprod (…) (Gam s)`; these restatements are syntactically in the form of the Blueprint.) -/
theorem g_mul_inv_cancel (a : G r s) : a * a⁻¹ = 1 := mul_inv_cancel a

theorem g_inv_mul_cancel (a : G r s) : a⁻¹ * a = 1 := inv_mul_cancel a

theorem g_inv_inv (a : G r s) : a⁻¹⁻¹ = a := inv_inv a

theorem g_inv_eq_of_mul_eq_one_right {a b : G r s} (h : a * b = 1) : a⁻¹ = b := by
  have h2 : a⁻¹ * (a * b) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, g_inv_mul_cancel, one_mul] at h2
  exact h2.symm

theorem g_map_inv {H : Type*} [Group H] (f : G r s →* H) (a : G r s) : f a⁻¹ = (f a)⁻¹ :=
  map_inv f a

/-! ## Letters -/
@[simp] theorem bar_bar (a : Lt r s) : bar (bar a) = a := by
  rcases a with ⟨i, b⟩ | j <;> simp [bar]

theorem genL_bar (a : Lt r s) : genL (bar a) = (genL a)⁻¹ := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · exact (g_inv_inv _).symm
    · rfl
  · simp only [bar, genL]
    refine (g_inv_eq_of_mul_eq_one_right ?_).symm
    rw [← map_mul, DerandSq.mGen_mul_self, map_one]

theorem genL_mul_genL_bar (a : Lt r s) : genL a * genL (bar a) = 1 := by
  rw [genL_bar, g_mul_inv_cancel]

/-! ## Word products -/
@[simp] theorem wprod_nil : wprod ([] : List (Lt r s)) = 1 := rfl

@[simp] theorem wprod_cons (a : Lt r s) (u : List (Lt r s)) :
    wprod (a :: u) = genL a * wprod u := by
  simp [wprod]

@[simp] theorem wprod_append (u v : List (Lt r s)) : wprod (u ++ v) = wprod u * wprod v := by
  simp [wprod]

/-! ## The push action on reduced words -/
/-- Cancel the head if it is the inverse letter, otherwise push. -/
def push (a : Lt r s) : List (Lt r s) → List (Lt r s)
  | [] => [a]
  | b :: t => if b = bar a then t else a :: b :: t

@[simp] theorem push_nil (a : Lt r s) : push a [] = [a] := rfl

theorem push_cons_bar (a : Lt r s) (t : List (Lt r s)) : push a (bar a :: t) = t := by
  simp [push]

theorem push_cons_ne (a b : Lt r s) (t : List (Lt r s)) (h : b ≠ bar a) :
    push a (b :: t) = a :: b :: t := by
  simp [push, h]

theorem red_nil : Red ([] : List (Lt r s)) := List.isChain_nil

theorem red_cons_cons {a b : Lt r s} {t : List (Lt r s)} :
    Red (a :: b :: t) ↔ b ≠ bar a ∧ Red (b :: t) := List.isChain_cons_cons

theorem Red.tail' {a : Lt r s} {t : List (Lt r s)} (h : Red (a :: t)) : Red t :=
  List.IsChain.tail h

theorem red_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) : Red (push a u) := by
  cases u with
  | nil => exact List.isChain_singleton _
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; exact Red.tail' h
    · rw [push_cons_ne _ _ _ hb]; exact red_cons_cons.2 ⟨hb, h⟩

theorem push_bar_push (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push (bar a) (push a u) = u := by
  cases u with
  | nil => simp [push]
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar]
      cases t with
      | nil => rfl
      | cons c t =>
        have hc : c ≠ bar (bar a) := (red_cons_cons.1 h).1
        rw [push_cons_ne _ _ _ hc]
    · rw [push_cons_ne _ _ _ hb]
      simp [push]

theorem push_push_bar (a : Lt r s) (u : List (Lt r s)) (h : Red u) :
    push a (push (bar a) u) = u := by
  simpa using push_bar_push (bar a) u h

theorem length_push_le (a : Lt r s) (u : List (Lt r s)) :
    (push a u).length ≤ u.length + 1 := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb; rw [push_cons_bar]; simp; omega
    · rw [push_cons_ne _ _ _ hb]; simp

theorem wprod_push (a : Lt r s) (u : List (Lt r s)) : wprod (push a u) = genL a * wprod u := by
  cases u with
  | nil => simp
  | cons b t =>
    by_cases hb : b = bar a
    · subst hb
      rw [push_cons_bar, wprod_cons, ← mul_assoc, genL_mul_genL_bar, one_mul]
    · rw [push_cons_ne _ _ _ hb]; simp

/-- Reduced words. -/
abbrev RL (r s : ℕ) := {u : List (Lt r s) // Red u}

/-- The permutation of reduced words given by a letter. -/
def pushP (a : Lt r s) : Equiv.Perm (RL r s) where
  toFun u := ⟨push a u.1, red_push a u.1 u.2⟩
  invFun u := ⟨push (bar a) u.1, red_push (bar a) u.1 u.2⟩
  left_inv u := Subtype.ext (push_bar_push a u.1 u.2)
  right_inv u := Subtype.ext (push_push_bar a u.1 u.2)

@[simp] theorem pushP_apply (a : Lt r s) (u : RL r s) : (pushP a u).1 = push a u.1 := rfl

theorem pushP_inv (a : Lt r s) : (pushP a)⁻¹ = pushP (bar a) := by
  ext u : 2
  rfl

theorem pushP_inr_sq (j : Fin s) :
    pushP (Sum.inr j : Lt r s) * pushP (Sum.inr j : Lt r s) = 1 := by
  have h := pushP_inv (Sum.inr j : Lt r s)
  have hb : bar (Sum.inr j : Lt r s) = Sum.inr j := rfl
  rw [hb] at h
  nth_rewrite 1 [← h]
  exact inv_mul_cancel _

/-- The homomorphism `Z₂ → Perm α` of an involution. -/
def invHomP {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    Multiplicative (ZMod 2) →* Equiv.Perm α where
  toFun a := σ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ a b : ZMod 2, σ ^ (a + b).val = σ ^ a.val * σ ^ b.val := by
      intro a b
      fin_cases a <;> fin_cases b
      · show σ ^ (0 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (0 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        simp
      · show σ ^ (1 : ZMod 2).val = σ ^ (1 : ZMod 2).val * σ ^ (0 : ZMod 2).val
        simp
      · show σ ^ ((1 : ZMod 2) + 1).val = σ ^ (1 : ZMod 2).val * σ ^ (1 : ZMod 2).val
        have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
        rw [h11]; simp [ZMod.val_one, hσ]
    exact key _ _

theorem invHomP_gen {α : Type*} (σ : Equiv.Perm α) (hσ : σ * σ = 1) :
    invHomP σ hσ (Multiplicative.ofAdd (1 : ZMod 2)) = σ := by
  show σ ^ (1 : ZMod 2).val = σ
  simp [ZMod.val_one]

/-- The action of `G r s` on reduced words. -/
def hom (r s : ℕ) : G r s →* Equiv.Perm (RL r s) :=
  Monoid.Coprod.lift (FreeGroup.lift fun i => pushP (Sum.inl (i, true)))
    (Monoid.CoprodI.lift fun j => invHomP (pushP (Sum.inr j)) (pushP_inr_sq j))

theorem hom_genL (a : Lt r s) : hom r s (genL a) = pushP a := by
  rcases a with ⟨i, b⟩ | j
  · cases b
    · have : hom r s (genL (Sum.inl (i, true))) = pushP (Sum.inl (i, true)) := by
        simp [hom, genL]
      show hom r s (genL (Sum.inl (i, true)))⁻¹ = _
      rw [g_map_inv, this, pushP_inv]; rfl
    · simp [hom, genL]
  · simp only [hom, genL, Monoid.Coprod.lift_apply_inr, DerandSq.mGen]
    rw [Monoid.CoprodI.lift_of]
    exact invHomP_gen _ _

/-- The normal form: the reduced word of `g`. -/
def nf (g : G r s) : List (Lt r s) := (hom r s g ⟨[], red_nil⟩).1

@[simp] theorem nf_one : nf (1 : G r s) = [] := by simp [nf]

theorem hom_genL_mul (a : Lt r s) (g : G r s) (v : RL r s) :
    (hom r s (genL a * g) v).1 = push a (hom r s g v).1 := by
  rw [map_mul, hom_genL]; rfl

theorem wprod_hom (g : G r s) : ∀ v : RL r s, wprod (hom r s g v).1 = g * wprod v.1 := by
  have hone : ∀ v : RL r s, wprod (hom r s 1 v).1 = 1 * wprod v.1 := by intro v; simp
  have hmul : ∀ x y : G r s, (∀ v : RL r s, wprod (hom r s x v).1 = x * wprod v.1) →
      (∀ v : RL r s, wprod (hom r s y v).1 = y * wprod v.1) →
      ∀ v : RL r s, wprod (hom r s (x * y) v).1 = x * y * wprod v.1 := by
    intro x y hx hy v
    rw [map_mul, Equiv.Perm.mul_apply, hx, hy, mul_assoc]
  have hgen : ∀ (a : Lt r s) (v : RL r s),
      wprod (hom r s (genL a) v).1 = genL a * wprod v.1 := by
    intro a v
    rw [hom_genL, pushP_apply, wprod_push]
  induction g using Monoid.Coprod.induction_on with
  | inl x =>
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of i => exact hgen (Sum.inl (i, true))
    | inv_of i _ => exact hgen (Sum.inl (i, false))
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | inr y =>
    induction y using Monoid.CoprodI.induction_on with
    | one => simp
    | of j m =>
      have hm : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd 1 := by decide
      rcases hm m with rfl | rfl
      · simp
      · exact hgen (Sum.inr j)
    | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy
  | mul x y hx hy => exact hmul x y hx hy

theorem wprod_nf (g : G r s) : wprod (nf g) = g := by
  have := wprod_hom g ⟨[], red_nil⟩
  simpa [nf] using this

theorem length_hom_wprod_le (u : List (Lt r s)) (v : RL r s) :
    (hom r s (wprod u) v).1.length ≤ u.length + v.1.length := by
  induction u with
  | nil => simp
  | cons a t ih =>
    rw [wprod_cons, hom_genL_mul]
    have := length_push_le a (hom r s (wprod t) v).1
    simp only [List.length_cons]
    omega

theorem length_nf_wprod_le (u : List (Lt r s)) : (nf (wprod u)).length ≤ u.length := by
  have := length_hom_wprod_le u ⟨[], red_nil⟩
  simp only [List.length_nil, add_zero] at this
  exact this

/-- Any word for `g` bounds `len g`. -/
theorem len_le_of_wprod {u : List (Lt r s)} {g : G r s} (h : wprod u = g) : len g ≤ u.length :=
  Nat.sInf_le ⟨u, rfl, h⟩

theorem len_eq_length_nf (g : G r s) : len g = (nf g).length := by
  apply le_antisymm (len_le_of_wprod (wprod_nf g))
  have hne : {n | ∃ u : List (Lt r s), u.length = n ∧ wprod u = g}.Nonempty :=
    ⟨_, nf g, rfl, wprod_nf g⟩
  obtain ⟨u, hu, hg⟩ := Nat.sInf_mem hne
  show _ ≤ len g
  unfold len
  rw [← hu, ← hg]
  exact length_nf_wprod_le u

@[simp] theorem len_one : len (1 : G r s) = 0 := by rw [len_eq_length_nf, nf_one]; rfl

/-! ## Aliases -/

/-! ## Generic group identities

(`simp`, `rw` and `group` do not see through the instance path of `G r s`, so identities are
proved in a generic group and applied with `exact`.) -/

/-! ## The inverse word -/
/-- The inverse word: reversed, with `bar` applied. -/
def ibar (u : List (Lt r s)) : List (Lt r s) := (u.map bar).reverse

@[simp] theorem ibar_nil : ibar ([] : List (Lt r s)) = [] := rfl

@[simp] theorem length_ibar (u : List (Lt r s)) : (ibar u).length = u.length := by simp [ibar]

/-! ## Non-reduced words are not shortest -/

/-! ## Repeated words -/
/-- `Z` repeated `k` times. -/
def rep (Z : List (Lt r s)) (k : ℕ) : List (Lt r s) := (List.replicate k Z).flatten

@[simp] theorem rep_zero (Z : List (Lt r s)) : rep Z 0 = [] := by simp [rep]

theorem rep_succ (Z : List (Lt r s)) (k : ℕ) : rep Z (k + 1) = Z ++ rep Z k := by
  simp [rep, List.replicate_succ]

@[simp] theorem rep_nil (k : ℕ) : rep ([] : List (Lt r s)) k = [] := by simp [rep]

@[simp] theorem length_rep (Z : List (Lt r s)) (k : ℕ) : (rep Z k).length = k * Z.length := by
  induction k with
  | zero => simp
  | succ k ih => rw [rep_succ, List.length_append, ih]; ring

end RandomInvolutions.Dev.PartW
end
end

section
open Finset Filter Topology Polynomial BordenaveCollins
open scoped Classical
open ZigZagStrong
open ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology
theorem solution (r : ℕ) :
    StrongConvergence (fun n => finiteLaw (Ω := Fin r → Involution (n+2)))
      (fun _ τ i => StrongConv.permOpPerp (τ i).val)
      (fun i => regularL2 (involutionGenerator i)) := by
  exact ZigZagStrong.ZigZag.involution_strong_convergence_dev r
end
