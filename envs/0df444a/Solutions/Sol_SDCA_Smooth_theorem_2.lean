-- Prove2me | solution 1 for SDCA.Smooth.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T12:04:21.579162+00:00
-- url     : https://prove2.me/submissions/817c956d-ef1d-4a01-a150-2630d671ea5b

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

-- Complete module: SDProof/SharedBasics.lean

-- Complete module: SDProof/ConjugateBasics.lean
namespace SDCA.Smooth.SDFresh
open SDCA.Lipschitz

theorem conj_lower (f : ℝ → ℝ) (u z : ℝ) : ((z*u-f z : ℝ) : EReal) ≤ conj f u :=
  le_iSup (fun z : ℝ => ((z*u-f z : ℝ) : EReal)) z

theorem conj_ne_bot (f : ℝ → ℝ) (u : ℝ) : conj f u ≠ ⊥ := by
  have h := conj_lower f u 0
  intro he
  rw [he] at h
  simp at h

theorem conj_zero_le (f : ℝ → ℝ) (hf : ∀ z, 0 ≤ f z) : conj f 0 ≤ 0 := by
  apply iSup_le
  intro z
  exact_mod_cast (show z*0-f z ≤ 0 by linarith [hf z])

theorem conj_coe (f : ℝ → ℝ) (u : ℝ) (h : conj f u ≠ ⊤) :
    ((conj f u).toReal : EReal) = conj f u :=
  EReal.coe_toReal h (conj_ne_bot f u)

theorem tangent_le {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) {a g : ℝ}
    (hd : HasDerivAt f g a) (z : ℝ) : f a + g*(z-a) ≤ f z := by
  rcases lt_trichotomy a z with haz | rfl | hza
  · have h := hc.le_slope_of_hasDerivAt (Set.mem_univ a) (Set.mem_univ z) haz hd
    rw [slope_def_field] at h
    have := (le_div_iff₀ (sub_pos.mpr haz)).mp h
    linarith
  · simp
  · have h := hc.slope_le_of_hasDerivAt (Set.mem_univ z) (Set.mem_univ a) hza hd
    rw [slope_def_field] at h
    have := (div_le_iff₀ (sub_pos.mpr hza)).mp h
    nlinarith

theorem conj_at_deriv {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) {a g : ℝ}
    (hd : HasDerivAt f g a) : conj f g = ((a*g-f a : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro z
    exact_mod_cast (show z*g-f z ≤ a*g-f a by nlinarith [tangent_le hc hd z])
  · exact conj_lower f g a

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/DualBasics.lean
namespace SDCA.Smooth.SDFresh
open scoped InnerProductSpace

def Feasible {n : ℕ} (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) : Prop :=
  ∀ i, SDCA.Lipschitz.conj (φ i) (-α i) ≠ ⊤

noncomputable def dualReal {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) : ℝ :=
  (1/(n:ℝ)) * ∑ i, -(SDCA.Lipschitz.conj (φ i) (-α i)).toReal - lam/2 * ‖wOf lam x α‖^2

noncomputable def gap {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) : ℝ :=
  primal lam x φ (wOf lam x α) - dualReal lam x φ α

theorem feasible_zero {n : ℕ} (φ : Fin n → ℝ → ℝ) (hf : ∀ i z, 0 ≤ φ i z) :
    Feasible φ 0 := by
  intro i
  simp only [Pi.zero_apply, neg_zero]
  exact ne_of_lt ((conj_zero_le (φ i) (hf i)).trans_lt (by simp))

theorem coe_sum_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, EReal.coe_add, ih]

theorem dualReal_coe {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) (hα : Feasible φ α) :
    (dualReal lam x φ α : EReal) = dual lam x φ α := by
  simp only [dualReal, dual, EReal.coe_sub, EReal.coe_mul, coe_sum_real, EReal.coe_neg,
    conj_coe _ _ (hα _)]

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/ModelAlgebra.lean
namespace SDCA.Smooth.SDFresh
open scoped InnerProductSpace

@[simp] theorem wOf_zero {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) :
    wOf lam x 0 = 0 := by simp [wOf]

theorem inner_wOf {d n : ℕ} (hn : 0 < n) (lam : ℝ) (hl : 0 < lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (α : Fin n → ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    (1/(n:ℝ))*∑ i, α i*⟪w,x i⟫_ℝ = lam*⟪w,wOf lam x α⟫_ℝ := by
  simp only [wOf, inner_smul_right, inner_sum]
  field_simp

theorem wOf_step {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (α : Fin n → ℝ) (i : Fin n) :
    wOf lam x (SDCA.Lipschitz.sdcaStep Δ α i) =
      wOf lam x α + (lam*n)⁻¹ • (Δ α i • x i) := by
  classical
  simp only [wOf, SDCA.Lipschitz.sdcaStep, Pi.add_apply, add_smul, Finset.sum_add_distrib,
    smul_add]
  congr 1
  simp [Pi.single_apply, one_div]

theorem gap_identity_real {d n : ℕ} (hn : 0 < n) (lam : ℝ) (hl : 0 < lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) :
    gap lam x φ α = (1/(n:ℝ))*∑ i,
      (φ i ⟪wOf lam x α,x i⟫_ℝ + (SDCA.Lipschitz.conj (φ i) (-α i)).toReal + α i*⟪wOf lam x α,x i⟫_ℝ) := by
  have h := inner_wOf hn lam hl x α (wOf lam x α)
  rw [real_inner_self_eq_norm_sq] at h
  simp only [gap, primal, dualReal, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  linarith

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/CoordinateStep.lean
namespace SDCA.Smooth.SDFresh
open scoped InnerProductSpace

noncomputable def coordReal {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) (i : Fin n) (δ : ℝ) : ℝ :=
  -(SDCA.Lipschitz.conj (φ i) (-(α i+δ))).toReal -
    lam*n/2*‖wOf lam x α+(lam*n)⁻¹ • (δ • x i)‖^2

theorem coordReal_coe {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) (i : Fin n) (δ : ℝ)
    (hf : SDCA.Lipschitz.conj (φ i) (-(α i+δ)) ≠ ⊤) :
    (coordReal lam x φ α i δ : EReal) = coordObj lam x φ α i δ := by
  simp only [coordReal, coordObj, EReal.coe_sub, EReal.coe_neg, conj_coe _ _ hf]

theorem feasible_step {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (α : Fin n → ℝ) (hα : Feasible φ α) (i : Fin n) :
    Feasible φ (SDCA.Lipschitz.sdcaStep Δ α i) := by
  classical
  have hc : SDCA.Lipschitz.conj (φ i) (-(α i+Δ α i)) ≠ ⊤ := by
    have h := hΔ α i 0
    rw [← coordReal_coe lam x φ α i 0 (by simpa using hα i)] at h
    intro he
    unfold coordObj at h
    rw [he] at h
    simp at h
  intro j
  by_cases hj : j = i
  · subst j
    simpa [SDCA.Lipschitz.sdcaStep] using hc
  · simpa [SDCA.Lipschitz.sdcaStep, Pi.single_apply, hj] using hα j

theorem coordReal_max {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (α : Fin n → ℝ) (hα : Feasible φ α) (i : Fin n) (δ : ℝ)
    (hf : SDCA.Lipschitz.conj (φ i) (-(α i+δ)) ≠ ⊤) :
    coordReal lam x φ α i δ ≤ coordReal lam x φ α i (Δ α i) := by
  have hc : SDCA.Lipschitz.conj (φ i) (-(α i+Δ α i)) ≠ ⊤ := by
    simpa [SDCA.Lipschitz.sdcaStep] using feasible_step lam x φ Δ hΔ α hα i i
  have h := hΔ α i δ
  rw [← coordReal_coe lam x φ α i δ hf, ← coordReal_coe lam x φ α i (Δ α i) hc] at h
  exact_mod_cast h

theorem step_dual_difference {d n : ℕ} (hn : 0 < n) (lam : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (α : Fin n → ℝ) (i : Fin n) :
    (n:ℝ)*(dualReal lam x φ (SDCA.Lipschitz.sdcaStep Δ α i)-dualReal lam x φ α) =
      coordReal lam x φ α i (Δ α i)-coordReal lam x φ α i 0 := by
  classical
  have he : ∑ j, -(SDCA.Lipschitz.conj (φ j) (-SDCA.Lipschitz.sdcaStep Δ α i j)).toReal =
      -(SDCA.Lipschitz.conj (φ i) (-(α i+Δ α i))).toReal +
        ∑ j ∈ Finset.univ.erase i, -(SDCA.Lipschitz.conj (φ j) (-α j)).toReal := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp [SDCA.Lipschitz.sdcaStep]
    · apply Finset.sum_congr rfl
      intro j hj
      simp [SDCA.Lipschitz.sdcaStep, (Finset.mem_erase.mp hj).1]
  have he0 : ∑ j, -(SDCA.Lipschitz.conj (φ j) (-α j)).toReal =
      -(SDCA.Lipschitz.conj (φ i) (-α i)).toReal +
        ∑ j ∈ Finset.univ.erase i, -(SDCA.Lipschitz.conj (φ j) (-α j)).toReal :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  simp only [dualReal, he, he0, wOf_step, coordReal, add_zero, zero_smul, smul_zero]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/ScalarSmooth.lean
namespace SDCA.Smooth.SDFresh

theorem scalar_descent (f f' : ℝ → ℝ) (L : ℝ) (hd : ∀ z, HasDerivAt f (f' z) z)
    (hL : ∀ a b, |f' a-f' b| ≤ L*|a-b|) (a b : ℝ) :
    f b ≤ f a + f' a*(b-a) + L/2*(b-a)^2 := by
  let q : ℝ → ℝ := fun z => f z - f a - f' a*(z-a) - L/2*(z-a)^2
  have hq (z : ℝ) : HasDerivAt q (f' z-f' a-L*(z-a)) z := by
    have h := (((hd z).sub_const (f a)).sub (((hasDerivAt_id z).sub_const a).const_mul (f' a))).sub
      ((((hasDerivAt_id z).sub_const a).pow 2).const_mul (L/2)) 
    exact h.congr_deriv (by simp only [id_eq]; ring)
  have hc : Continuous q := continuous_iff_continuousAt.mpr fun z => (hq z).continuousAt
  have hdiff : Differentiable ℝ q := fun z => (hq z).differentiableAt
  have hqa : q a = 0 := by simp [q]
  rcases le_total a b with hab | hba
  · have hm : AntitoneOn q (Set.Ici a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have haz : a ≤ z := (interior_subset hz)
      have h := (abs_le.mp (hL z a)).2
      rw [abs_of_nonneg (sub_nonneg.mpr haz)] at h
      linarith
    have h := hm (by simp) hab hab
    rw [hqa] at h
    dsimp [q] at h
    linarith
  · have hm : MonotoneOn q (Set.Iic a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic a) hc.continuousOn hdiff.differentiableOn
      intro z hz
      rw [(hq z).deriv]
      have hza : z ≤ a := (interior_subset (s := Set.Iic a) hz)
      have h := (abs_le.mp (hL z a)).1
      rw [abs_of_nonpos (sub_nonpos.mpr hza)] at h
      linarith
    have h := hm hba (by simp) hba
    rw [hqa] at h
    dsimp [q] at h
    linarith

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/ConjugateSmooth.lean
namespace SDCA.Smooth.SDFresh
open SDCA.Lipschitz

theorem conj_quadratic (f f' : ℝ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hd : ∀ z, HasDerivAt f (f' z) z) (hs : ∀ a b, |f' a-f' b| ≤ (1/γ)*|a-b|)
    (u z : ℝ) (hu : conj f u ≠ ⊤) :
    z*u-f z + γ/2*(u-f' z)^2 ≤ (conj f u).toReal := by
  have h1 := conj_lower f u (z+γ*(u-f' z))
  rw [← conj_coe f u hu] at h1
  have h1' : (z+γ*(u-f' z))*u-f (z+γ*(u-f' z)) ≤ (conj f u).toReal := by exact_mod_cast h1
  have h2 := scalar_descent f f' (1/γ) hd hs z (z+γ*(u-f' z))
  have he : (1/γ)/2*((z+γ*(u-f' z))-z)^2 = γ/2*(u-f' z)^2 := by field_simp; ring
  rw [he] at h2
  nlinarith

theorem conj_mix (f f' : ℝ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hd : ∀ z, HasDerivAt f (f' z) z) (hs : ∀ a b, |f' a-f' b| ≤ (1/γ)*|a-b|)
    (u v s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hu : conj f u ≠ ⊤) (hv : conj f v ≠ ⊤) :
    conj f (s*u+(1-s)*v) ≤
      ((s*(conj f u).toReal+(1-s)*(conj f v).toReal-γ/2*s*(1-s)*(u-v)^2 : ℝ) : EReal) := by
  apply iSup_le
  intro z
  have h1 := mul_le_mul_of_nonneg_left (conj_quadratic f f' γ hγ hd hs u z hu) hs0
  have h2 := mul_le_mul_of_nonneg_left (conj_quadratic f f' γ hγ hd hs v z hv) (sub_nonneg.mpr hs1)
  have hq := sq_nonneg (s*u+(1-s)*v-f' z)
  have he : s*(u-f' z)^2+(1-s)*(v-f' z)^2 =
      s*(1-s)*(u-v)^2+(s*u+(1-s)*v-f' z)^2 := by ring
  exact_mod_cast (show z*(s*u+(1-s)*v)-f z ≤
    s*(conj f u).toReal+(1-s)*(conj f v).toReal-γ/2*s*(1-s)*(u-v)^2 by nlinarith)

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/CoordinateImprovement.lean
namespace SDCA.Smooth.SDFresh
open scoped InnerProductSpace
open SDCA.Lipschitz

theorem coord_difference {d n : ℕ} (hn : 0 < n) (lam : ℝ) (hl : 0 < lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (α : Fin n → ℝ) (i : Fin n) (δ : ℝ) :
    coordReal lam x φ α i δ - coordReal lam x φ α i 0 =
      (conj (φ i) (-α i)).toReal - (conj (φ i) (-(α i+δ))).toReal -
      δ*⟪wOf lam x α,x i⟫_ℝ - δ^2*‖x i‖^2/(2*lam*n) := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hl' := ne_of_gt hl
  simp only [coordReal, add_zero, zero_smul, smul_zero, norm_add_sq_real,
    inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

theorem coordinate_improvement {d n : ℕ} (hn : 0 < n) (lam γ : ℝ) (hl : 0 < lam) (hγ : 0 < γ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ φ' : Fin n → ℝ → ℝ)
    (hc : ∀ i, ConvexOn ℝ Set.univ (φ i)) (hd : ∀ i z, HasDerivAt (φ i) (φ' i z) z)
    (hs : ∀ i a b, |φ' i a-φ' i b| ≤ (1/γ)*|a-b|)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : SDCA.Smooth.IsSDCAStep lam x φ Δ)
    (α : Fin n → ℝ) (hα : Feasible φ α) (i : Fin n) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hcoef : s*‖x i‖^2 ≤ γ*(1-s)*(lam*n)) :
    s*(φ i ⟪wOf lam x α,x i⟫_ℝ+(conj (φ i) (-α i)).toReal+α i*⟪wOf lam x α,x i⟫_ℝ) ≤
      coordReal lam x φ α i (Δ α i)-coordReal lam x φ α i 0 := by
  let z := ⟪wOf lam x α,x i⟫_ℝ
  let u := -φ' i z
  have hu : conj (φ i) (-u) = ((-u*z-φ i z : ℝ) : EReal) := by
    simpa [u, mul_comm] using conj_at_deriv (hc i) (hd i z)
  have huf : conj (φ i) (-u) ≠ ⊤ := by rw [hu]; exact EReal.coe_ne_top _
  have hm := conj_mix (φ i) (φ' i) γ hγ (hd i) (hs i) (-u) (-α i) s hs0.le hs1 huf (hα i)
  have he : s*(-u)+(1-s)*(-α i) = -(α i+s*(u-α i)) := by ring
  rw [he] at hm
  have hmf : conj (φ i) (-(α i+s*(u-α i))) ≠ ⊤ := ne_of_lt (hm.trans_lt (EReal.coe_lt_top _))
  rw [← conj_coe _ _ hmf, hu, EReal.toReal_coe] at hm
  have hm' : (conj (φ i) (-(α i+s*(u-α i)))).toReal ≤
      s*(-u*z-φ i z)+(1-s)*(conj (φ i) (-α i)).toReal-γ/2*s*(1-s)*((-u)-(-α i))^2 := by exact_mod_cast hm
  have hmax := coordReal_max lam x φ Δ hΔ α hα i (s*(u-α i)) hmf
  have heq := coord_difference hn lam hl x φ α i (s*(u-α i))
  have hden : 0 < 2*lam*(n:ℝ) := by positivity
  have hpos : 0 ≤ γ/2*s*(1-s)*(u-α i)^2 - (s*(u-α i))^2*‖x i‖^2/(2*lam*n) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hcoef (mul_nonneg hs0.le (sq_nonneg (u-α i)))
    nlinarith
  dsimp [z] at hm' heq
  nlinarith

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/OneStep.lean
namespace SDCA.Smooth.SDFresh
open scoped InnerProductSpace

theorem one_step_gap {d n : ℕ} (hn : 0 < n) (lam γ : ℝ) (hl : 0 < lam) (hγ : 0 < γ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ φ' : Fin n → ℝ → ℝ)
    (hc : ∀ i, ConvexOn ℝ Set.univ (φ i)) (hd : ∀ i z, HasDerivAt (φ i) (φ' i z) z)
    (hs : ∀ i a b, |φ' i a-φ' i b| ≤ (1/γ)*|a-b|)
    (hx : ∀ i, ‖x i‖ ≤ 1)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (α : Fin n → ℝ) (hα : Feasible φ α) :
    (n+1/(lam*γ))⁻¹ * gap lam x φ α ≤
      (1/(n:ℝ))*∑ i, dualReal lam x φ (SDCA.Lipschitz.sdcaStep Δ α i) - dualReal lam x φ α := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  let s : ℝ := lam*n*γ/(1+lam*n*γ)
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; apply (div_le_one (by positivity)).mpr; linarith
  have hrel : γ*(1-s)*(lam*n) = s := by dsimp [s]; field_simp; ring
  have hi (i : Fin n) := coordinate_improvement hn lam γ hl hγ x φ φ' hc hd hs Δ hΔ α hα i s hs0 hs1 (by
    rw [hrel]
    have hsq : ‖x i‖^2 ≤ 1 := by nlinarith [hx i, norm_nonneg (x i)]
    nlinarith)
  have ht := Finset.sum_le_sum (s := Finset.univ) fun i _ => hi i
  have he (i : Fin n) := step_dual_difference hn lam x φ Δ α i
  simp_rw [← he] at ht
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at ht
  have hg := gap_identity_real hn lam hl x φ α
  have hr : s/(n:ℝ) = (n+1/(lam*γ))⁻¹ := by
    dsimp [s]
    field_simp
    ring
  rw [← hr, hg]
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 1/(n:ℝ)^2 by positivity)
  calc
    _ = (1/(n:ℝ)^2) * (s * ∑ i, (φ i ⟪wOf lam x α,x i⟫_ℝ +
        (Lipschitz.conj (φ i) (-α i)).toReal + α i*⟪wOf lam x α,x i⟫_ℝ)) := by ring
    _ ≤ _ := hh
    _ = _ := by field_simp

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/DualBounds.lean
namespace SDCA.Smooth.SDFresh
open scoped InnerProductSpace

theorem dualReal_zero_nonneg {d n : ℕ} (hn : 0 < n) (lam : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (hf : ∀ i z, 0 ≤ φ i z) : 0 ≤ dualReal lam x φ 0 := by
  have hp := feasible_zero φ hf
  have hc (i : Fin n) : (SDCA.Lipschitz.conj (φ i) 0).toReal ≤ 0 := by
    have h := conj_zero_le (φ i) (hf i)
    rw [← conj_coe (φ i) 0 (by simpa using hp i)] at h
    exact_mod_cast h
  simp only [dualReal, Pi.zero_apply, neg_zero, wOf_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => neg_nonneg.mpr (hc i))

theorem primal_zero_le_one {d n : ℕ} (hn : 0 < n) (lam : ℝ)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (hf : ∀ i, φ i 0 ≤ 1) : primal lam x φ 0 ≤ 1 := by
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hf i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  simp only [primal, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ hn').mpr (by simpa using hsum)

theorem weak_duality_real {d n : ℕ} (hn : 0 < n) (lam : ℝ) (hl : 0 < lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (α : Fin n → ℝ) (hα : Feasible φ α) (w : EuclideanSpace ℝ (Fin d)) :
    dualReal lam x φ α ≤ primal lam x φ w := by
  have hc (i : Fin n) : -α i*⟪w,x i⟫_ℝ-φ i ⟪w,x i⟫_ℝ ≤
      (SDCA.Lipschitz.conj (φ i) (-α i)).toReal := by
    have h := conj_lower (φ i) (-α i) ⟪w,x i⟫_ℝ
    rw [← conj_coe (φ i) (-α i) (hα i)] at h
    have h' : ⟪w,x i⟫_ℝ *(-α i)-φ i ⟪w,x i⟫_ℝ ≤ (SDCA.Lipschitz.conj (φ i) (-α i)).toReal := by exact_mod_cast h
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hc i
  simp only [Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib] at hsum
  have hs := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1/(n:ℝ) by positivity)
  have hi := inner_wOf hn lam hl x α w
  have hnorm := norm_sub_sq_real w (wOf lam x α)
  have hp : 0 ≤ lam/2*‖w-wOf lam x α‖^2 := by positivity
  dsimp [dualReal, primal]
  simp only [Finset.sum_neg_distrib]
  nlinarith

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/DualSupremum.lean

namespace SDCA.Smooth.SDFresh

noncomputable def dualSup {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) : ℝ :=
  sSup {v | ∃ α, Feasible φ α ∧ dualReal lam x φ α = v}

theorem dual_values_nonempty {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hf : ∀ i z, 0 ≤ φ i z) :
    ({v | ∃ α, Feasible φ α ∧ dualReal lam x φ α = v} : Set ℝ).Nonempty :=
  ⟨_, 0, feasible_zero φ hf, rfl⟩

theorem dual_values_bdd {d n : ℕ} (hn : 0<n) (lam : ℝ) (hl : 0<lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ) :
    BddAbove {v | ∃ α, Feasible φ α ∧ dualReal lam x φ α = v} := by
  refine ⟨primal lam x φ 0, ?_⟩
  rintro v ⟨α,hα,rfl⟩
  exact weak_duality_real hn lam hl x φ α hα 0

theorem dual_le_sup {d n : ℕ} (hn : 0<n) (lam : ℝ) (hl : 0<lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (α : Fin n → ℝ) (hα : Feasible φ α) : dualReal lam x φ α ≤ dualSup lam x φ :=
  le_csSup (dual_values_bdd hn lam hl x φ) ⟨α,hα,rfl⟩

theorem dualSup_le_primal {d n : ℕ} (hn : 0<n) (lam : ℝ) (hl : 0<lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (hf : ∀ i z, 0 ≤ φ i z) (w : EuclideanSpace ℝ (Fin d)) :
    dualSup lam x φ ≤ primal lam x φ w := by
  apply csSup_le (dual_values_nonempty lam x φ hf)
  rintro v ⟨α,hα,rfl⟩
  exact weak_duality_real hn lam hl x φ α hα w

theorem initial_error_le_one {d n : ℕ} (hn : 0<n) (lam : ℝ) (hl : 0<lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (hf : ∀ i z, 0 ≤ φ i z) (h0 : ∀ i, φ i 0 ≤ 1) :
    dualSup lam x φ - dualReal lam x φ 0 ≤ 1 := by
  have h := dualSup_le_primal hn lam hl x φ hf 0
  have h' := primal_zero_le_one hn lam x φ h0
  have h'' := dualReal_zero_nonneg hn lam x φ hf
  linarith

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/FiniteExpectation.lean

namespace SDCA.Smooth.SDFresh

open SAGA.Convex

theorem expectIdx_mono {n T : ℕ} {f g : (Fin T → Fin n) → ℝ}
    (h : ∀ js, f js ≤ g js) : expectIdx n T f ≤ expectIdx n T g := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun js _ => h js)) (by positivity)

theorem expectIdx_add {n T : ℕ} (f g : (Fin T → Fin n) → ℝ) :
    expectIdx n T (fun js => f js+g js) = expectIdx n T f+expectIdx n T g := by
  unfold expectIdx
  rw [Finset.sum_add_distrib, mul_add]

theorem expectIdx_sub {n T : ℕ} (f g : (Fin T → Fin n) → ℝ) :
    expectIdx n T (fun js => f js-g js) = expectIdx n T f-expectIdx n T g := by
  unfold expectIdx
  rw [Finset.sum_sub_distrib, mul_sub]

theorem expectIdx_mul {n T : ℕ} (a : ℝ) (f : (Fin T → Fin n) → ℝ) :
    expectIdx n T (fun js => a*f js) = a*expectIdx n T f := by
  unfold expectIdx
  rw [← Finset.mul_sum]
  ring

theorem expectIdx_const {n T : ℕ} (hn : 0<n) (a : ℝ) :
    expectIdx n T (fun _ => a) = a := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [expectIdx, hn']

theorem expectIdx_finset_sum {n T : ℕ} {J : Type*} (s : Finset J)
    (f : J → (Fin T → Fin n) → ℝ) :
    expectIdx n T (fun js => ∑ j ∈ s, f j js) = ∑ j ∈ s, expectIdx n T (f j) := by
  unfold expectIdx
  rw [Finset.sum_comm, Finset.mul_sum]

theorem expectIdx_zero {n : ℕ} (f : (Fin 0 → Fin n) → ℝ) :
    expectIdx n 0 f = f (fun i => Fin.elim0 i) := by
  simpa only [expectIdx, pow_zero, div_one, one_mul, Fintype.sum_unique] using
    congrArg f (Subsingleton.elim (default : Fin 0 → Fin n) (fun i => Fin.elim0 i))

theorem expectIdx_snoc {n T : ℕ} (hn : 0<n) (f : (Fin (T+1) → Fin n) → ℝ) :
    expectIdx n (T+1) f = expectIdx n T (fun js => (1/(n:ℝ))*∑ i, f (Fin.snoc js i)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs := (Fin.snocEquiv (fun _ : Fin (T+1) => Fin n)).sum_comp f
  change (∑ z : Fin n × (Fin T → Fin n), f (Fin.snoc z.2 z.1)) = ∑ js, f js at hs
  unfold expectIdx
  rw [← hs, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [pow_succ]
  field_simp

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/RunBasics.lean

namespace SDCA.Smooth.SDFresh
open SAGA.Convex

theorem alphaIter_full {n T : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (js : Fin T → Fin n) :
    alphaIter Δ js T = (List.ofFn js).foldl (SDCA.Lipschitz.sdcaStep Δ) 0 := by
  unfold alphaIter
  rw [(List.take_eq_self_iff (List.ofFn js)).mpr (by simp)]

theorem ofFn_snoc_eq {n T : ℕ} (js : Fin T → Fin n) (i : Fin n) :
    List.ofFn (Fin.snoc js i) = List.ofFn js ++ [i] := by
  rw [List.ofFn_succ_last]
  simp

theorem alphaIter_snoc_full {n T : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (js : Fin T → Fin n) (i : Fin n) :
    alphaIter Δ (Fin.snoc js i) (T+1) = SDCA.Lipschitz.sdcaStep Δ (alphaIter Δ js T) i := by
  rw [alphaIter_full, ofFn_snoc_eq, List.foldl_append, alphaIter_full]
  rfl

theorem alphaIter_snoc_prefix {n T t : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (js : Fin T → Fin n) (i : Fin n) (ht : t ≤ T) :
    alphaIter Δ (Fin.snoc js i) t = alphaIter Δ js t := by
  unfold alphaIter
  rw [ofFn_snoc_eq, List.take_append_of_le_length (by simpa using ht)]

theorem expectIdx_prefix {n T t : ℕ} (hn : 0<n)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (F : (Fin n → ℝ) → ℝ) (ht : t≤T) :
    expectIdx n T (fun js => F (alphaIter Δ js t)) =
      expectIdx n t (fun js => F (alphaIter Δ js t)) := by
  induction T, ht using Nat.le_induction with
  | base => rfl
  | succ T ht ih =>
    rw [expectIdx_snoc hn]
    simp_rw [alphaIter_snoc_prefix Δ _ _ ht]
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simpa [hn'] using ih

theorem expectIdx_next {n T : ℕ} (hn : 0<n)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (F : (Fin n → ℝ) → ℝ) :
    expectIdx n (T+1) (fun js => F (alphaIter Δ js (T+1))) =
      expectIdx n T (fun js => (1/(n:ℝ))*∑ i,
        F (SDCA.Lipschitz.sdcaStep Δ (alphaIter Δ js T) i)) := by
  rw [expectIdx_snoc hn]
  simp_rw [alphaIter_snoc_full]

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/RunFeasible.lean

namespace SDCA.Smooth.SDFresh

theorem alphaIter_invariant {n T : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (P : (Fin n → ℝ) → Prop) (h0 : P 0)
    (hs : ∀ α, P α → ∀ i, P (SDCA.Lipschitz.sdcaStep Δ α i))
    (js : Fin T → Fin n) (t : ℕ) : P (alphaIter Δ js t) := by
  have hfold (l : List (Fin n)) (α : Fin n → ℝ) (hα : P α) :
      P (l.foldl (SDCA.Lipschitz.sdcaStep Δ) α) := by
    induction l generalizing α with
    | nil => exact hα
    | cons i l ih => exact ih _ (hs α hα i)
  exact hfold _ _ h0

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/ScalarRates.lean

namespace SDCA.Smooth.SDFresh

theorem error_exp_bound (E : ℕ → ℝ) (a : ℝ) (ha : a ≤ 1)
    (h0 : E 0 ≤ 1) (hstep : ∀ t, E (t+1) ≤ (1-a)*E t) (t : ℕ) :
    E t ≤ Real.exp (-a*t) := by
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    calc
      E (t+1) ≤ (1-a)*E t := hstep t
      _ ≤ (1-a)*Real.exp (-a*t) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ Real.exp (-a)*Real.exp (-a*t) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (-a)]) (Real.exp_pos _).le
      _ = Real.exp (-a*(t+1:ℕ)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

theorem log_rate_bound {c ε t : ℝ} (hc : 0<c) (hε : 0<ε)
    (ht : c*Real.log (c/ε) ≤ t) : c*Real.exp (-t/c) ≤ ε := by
  have hl : Real.log (c/ε) ≤ t/c := (le_div_iff₀ hc).mpr (by nlinarith [ht])
  have he : -t/c ≤ Real.log (ε/c) := by
    rw [Real.log_div (ne_of_gt hε) (ne_of_gt hc)]
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hε)] at hl
    rw [neg_div]
    linarith
  calc
    c*Real.exp (-t/c) ≤ c*Real.exp (Real.log (ε/c)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hc.le
    _ = ε := by rw [Real.exp_log (div_pos hε hc)]; field_simp

theorem log_window_bound {c ε t w : ℝ} (hc : 0<c) (hε : 0<ε) (hw : 0<w)
    (ht : c*Real.log (c/(w*ε)) ≤ t) : (c*Real.exp (-t/c))/w ≤ ε := by
  apply (div_le_iff₀ hw).mpr
  have h := log_rate_bound hc (mul_pos hw hε) ht
  nlinarith

theorem sum_decreases (E G : ℕ → ℝ) (a : ℝ) {s t : ℕ} (hst : s ≤ t)
    (h : ∀ j, a*G j ≤ E j-E (j+1)) :
    a * ∑ j ∈ Finset.Ico s t, G j ≤ E s-E t := by
  calc
    a * ∑ j ∈ Finset.Ico s t, G j = ∑ j ∈ Finset.Ico s t, a*G j := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.Ico s t, (E j-E (j+1)) := Finset.sum_le_sum (fun j _ => h j)
    _ = E s-E t := by
      rw [Finset.sum_Ico_eq_sub _ hst, Finset.sum_range_sub', Finset.sum_range_sub']
      ring

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/DriftRates.lean

namespace SDCA.Smooth.SDFresh
open SAGA.Convex

noncomputable def runMean {n : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ) (t : ℕ) : ℝ :=
  expectIdx n t (fun js => F (alphaIter Δ js t))

theorem runMean_zero {n : ℕ} (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (F : (Fin n → ℝ) → ℝ) : runMean Δ F 0 = F 0 := by
  rw [runMean, expectIdx_zero]
  simp [alphaIter]

theorem runMean_nonneg {n : ℕ} (hn : 0<n) (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (P : (Fin n → ℝ) → Prop) (h0 : P 0)
    (hs : ∀ α, P α → ∀ i, P (SDCA.Lipschitz.sdcaStep Δ α i))
    (F : (Fin n → ℝ) → ℝ) (hF : ∀ α, P α → 0≤F α) (t : ℕ) :
    0≤runMean Δ F t := by
  have h := expectIdx_mono (T := t) (fun js => hF _ (alphaIter_invariant Δ P h0 hs js t))
  simpa [runMean, expectIdx_const hn] using h

theorem runMean_drift {n : ℕ} (hn : 0<n) (Δ : (Fin n → ℝ) → Fin n → ℝ)
    (P : (Fin n → ℝ) → Prop) (h0 : P 0)
    (hs : ∀ α, P α → ∀ i, P (SDCA.Lipschitz.sdcaStep Δ α i))
    (E G : (Fin n → ℝ) → ℝ) (a : ℝ)
    (hd : ∀ α, P α → (1/(n:ℝ))*∑ i, E (SDCA.Lipschitz.sdcaStep Δ α i)
      ≤ E α-a*G α) (t : ℕ) :
    runMean Δ E (t+1) ≤ runMean Δ E t-a*runMean Δ G t := by
  rw [runMean, expectIdx_next hn]
  have h := expectIdx_mono (T := t) (fun js => hd _ (alphaIter_invariant Δ P h0 hs js t))
  simpa only [expectIdx_sub, expectIdx_mul, runMean] using h

theorem mean_error_bound (E G : ℕ → ℝ) (a : ℝ) (ha0 : 0≤a) (ha1 : a≤1)
    (h0 : E 0≤1) (hEG : ∀ t, E t≤G t)
    (hd : ∀ t, E (t+1)≤E t-a*G t) (t : ℕ) :
    E t≤Real.exp (-a*t) := by
  apply error_exp_bound E a ha1 h0 _ t
  intro j
  have h := mul_le_mul_of_nonneg_left (hEG j) ha0
  nlinarith [hd j]

theorem mean_gap_bound (E G : ℕ → ℝ) (a : ℝ) (ha0 : 0<a) (ha1 : a≤1)
    (h0 : E 0≤1) (hE : ∀ t, 0≤E t) (hEG : ∀ t, E t≤G t)
    (hd : ∀ t, E (t+1)≤E t-a*G t) (t : ℕ) :
    G t≤Real.exp (-a*t)/a := by
  apply (le_div_iff₀ ha0).mpr
  have h := mean_error_bound E G a ha0.le ha1 h0 hEG hd t
  nlinarith [hd t, hE (t+1)]

theorem mean_window_bound (E G : ℕ → ℝ) (a : ℝ) (ha0 : 0<a) (ha1 : a≤1)
    (h0 : E 0≤1) (hE : ∀ t, 0≤E t) (hEG : ∀ t, E t≤G t)
    (hd : ∀ t, E (t+1)≤E t-a*G t) {s t : ℕ} (hst : s<t) :
    (1/((t:ℝ)-s))*∑ j ∈ Finset.Ico s t, G j ≤
      (Real.exp (-a*s)/a)/((t:ℝ)-s) := by
  have hsum := sum_decreases E G a hst.le (fun j => by linarith [hd j])
  have he := mean_error_bound E G a ha0.le ha1 h0 hEG hd s
  have hw : 0 < (t:ℝ)-s := by
    have hst' : (s:ℝ)<t := by exact_mod_cast hst
    linarith
  have hb : (∑ j ∈ Finset.Ico s t, G j) ≤ Real.exp (-a*s)/a := by
    apply (le_div_iff₀ ha0).mpr
    nlinarith [hE t]
  simpa [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hw.le)

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/OperationalRates.lean

namespace SDCA.Smooth.SDFresh
open SAGA.Convex

theorem operational_rates {n : ℕ} (hn : 0<n)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (P : (Fin n → ℝ) → Prop) (h0 : P 0)
    (hs : ∀ α, P α → ∀ i, P (SDCA.Lipschitz.sdcaStep Δ α i))
    (E G : (Fin n → ℝ) → ℝ) (c : ℝ) (hc : 1≤c)
    (hE : ∀ α, P α → 0≤E α) (hEG : ∀ α, P α → E α≤G α)
    (hinit : E 0≤1)
    (hd : ∀ α, P α → (1/(n:ℝ))*∑ i, E (SDCA.Lipschitz.sdcaStep Δ α i)
      ≤ E α-(1/c)*G α) :
    (∀ t, runMean Δ G t ≤ c*Real.exp (-(t:ℝ)/c)) ∧
    (∀ s t : ℕ, s<t →
      (1/((t:ℝ)-s))*∑ j ∈ Finset.Ico s t,
        expectIdx n t (fun js => G (alphaIter Δ js j)) ≤
      (c*Real.exp (-(s:ℝ)/c))/((t:ℝ)-s)) := by
  have hc0 : 0<c := by linarith
  have ha0 : 0<1/c := one_div_pos.mpr hc0
  have ha1 : 1/c≤1 := (div_le_iff₀ hc0).mpr (by linarith)
  have he : ∀ t, 0≤runMean Δ E t := runMean_nonneg hn Δ P h0 hs E hE
  have heg (t : ℕ) : runMean Δ E t≤runMean Δ G t :=
    expectIdx_mono (fun js => hEG _ (alphaIter_invariant Δ P h0 hs js t))
  have hi : runMean Δ E 0≤1 := by simpa only [runMean_zero] using hinit
  have hstep := runMean_drift hn Δ P h0 hs E G (1/c) hd
  have hnrm (k : ℕ) : Real.exp (-(1/c)*k)/(1/c) = c*Real.exp (-(k:ℝ)/c) := by
    have hex : -(1/c)*(k:ℝ) = -(k:ℝ)/c := by ring
    rw [hex]
    field_simp
  constructor
  · intro t
    have h := mean_gap_bound (runMean Δ E) (runMean Δ G) (1/c) ha0 ha1 hi he heg hstep t
    simpa only [hnrm] using h
  · intro s t hst
    have h := mean_window_bound (runMean Δ E) (runMean Δ G) (1/c) ha0 ha1 hi he heg hstep hst
    have hp : (∑ j ∈ Finset.Ico s t, expectIdx n t (fun js => G (alphaIter Δ js j))) =
        ∑ j ∈ Finset.Ico s t, runMean Δ G j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact expectIdx_prefix hn Δ G (Finset.mem_Ico.mp hj).2.le
    rw [hp]
    simpa only [hnrm] using h

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/NativeRates.lean

namespace SDCA.Smooth.SDFresh

theorem native_rates {d n : ℕ} (hn : 0<n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ φ' : Fin n → ℝ → ℝ) (hc : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam γ : ℝ) (hl : 0<lam) (hγ : 0<γ)
    (hd : ∀ i a, HasDerivAt (φ i) (φ' i a) a)
    (hs : ∀ i a b, |φ' i a-φ' i b|≤(1/γ)*|a-b|)
    (hx : ∀ i, ‖x i‖≤1) (hf : ∀ i z, 0≤φ i z) (hf0 : ∀ i, φ i 0≤1)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ) :
    (∀ t, runMean Δ (gap lam x φ) t ≤
      (n+1/(lam*γ))*Real.exp (-(t:ℝ)/(n+1/(lam*γ)))) ∧
    (∀ s t : ℕ, s<t → (1/((t:ℝ)-s))*∑ j ∈ Finset.Ico s t,
      SAGA.Convex.expectIdx n t (fun js => gap lam x φ (alphaIter Δ js j)) ≤
      ((n+1/(lam*γ))*Real.exp (-(s:ℝ)/(n+1/(lam*γ))))/((t:ℝ)-s)) := by
  let E := fun α => dualSup lam x φ-dualReal lam x φ α
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (n:ℝ)≠0 := by positivity
  apply operational_rates hn Δ (Feasible φ) (feasible_zero φ hf)
    (fun α hα i => feasible_step lam x φ Δ hΔ α hα i) E (gap lam x φ)
    (n+1/(lam*γ)) (by
      have hp : 0<1/(lam*γ) := by positivity
      linarith)
  · intro α hα
    exact sub_nonneg.mpr (dual_le_sup hn lam hl x φ α hα)
  · intro α _
    have h := dualSup_le_primal hn lam hl x φ hf (wOf lam x α)
    dsimp [E, gap]
    linarith
  · exact initial_error_le_one hn lam hl x φ hf hf0
  · intro α hα
    have h := one_step_gap hn lam γ hl hγ x φ φ' hc hd hs hx Δ hΔ α hα
    change (n+1/(lam*γ))⁻¹ * gap lam x φ α ≤
      (1/(n:ℝ))*(∑ i, dualReal lam x φ (SDCA.Lipschitz.sdcaStep Δ α i))-
        dualReal lam x φ α at h
    dsimp [E]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have hdst : (1/(n:ℝ))*((n:ℝ)*dualSup lam x φ)=dualSup lam x φ := by field_simp
    rw [mul_sub, hdst]
    simp only [one_div] at h ⊢
    linarith

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/FeasibleConvex.lean
namespace SDCA.Smooth.SDFresh
open SDCA.Lipschitz

theorem conj_convex_bound (f : ℝ → ℝ) (u v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) (hu : conj f u ≠ ⊤) (hv : conj f v ≠ ⊤) :
    conj f (a*u+b*v) ≤ ((a*(conj f u).toReal+b*(conj f v).toReal : ℝ) : EReal) := by
  apply iSup_le
  intro z
  have h1 := conj_lower f u z
  have h2 := conj_lower f v z
  rw [← conj_coe _ _ hu] at h1
  rw [← conj_coe _ _ hv] at h2
  have h1' : z*u-f z ≤ (conj f u).toReal := by exact_mod_cast h1
  have h2' : z*v-f z ≤ (conj f v).toReal := by exact_mod_cast h2
  have h := add_le_add (mul_le_mul_of_nonneg_left h1' ha) (mul_le_mul_of_nonneg_left h2' hb)
  exact_mod_cast (show z*(a*u+b*v)-f z ≤ a*(conj f u).toReal+b*(conj f v).toReal by
    calc
      _ = a*(z*u-f z)+b*(z*v-f z) := by nlinarith [congrArg (fun t : ℝ => t*f z) hab]
      _ ≤ _ := h)

theorem feasible_convex {n : ℕ} (φ : Fin n → ℝ → ℝ) : Convex ℝ {α | Feasible φ α} := by
  intro α hα β hβ a b ha hb hab i
  have h := conj_convex_bound (φ i) (-α i) (-β i) a b ha hb hab (hα i) (hβ i)
  have he : -(a • α+b • β) i = a*(-α i)+b*(-β i) := by simp; ring
  rw [he]
  exact ne_of_lt (h.trans_lt (EReal.coe_lt_top _))

theorem conjugate_convex {n : ℕ} (φ : Fin n → ℝ → ℝ) (i : Fin n) :
    ConvexOn ℝ {α | Feasible φ α} (fun α => (conj (φ i) (-α i)).toReal) := by
  refine ⟨feasible_convex φ, ?_⟩
  intro α hα β hβ a b ha hb hab
  have hf := feasible_convex φ hα hβ ha hb hab
  have h := conj_convex_bound (φ i) (-α i) (-β i) a b ha hb hab (hα i) (hβ i)
  have he : -(a • α+b • β) i = a*(-α i)+b*(-β i) := by simp; ring
  rw [← he, ← conj_coe _ _ (hf i)] at h
  exact_mod_cast h

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/GapConvex.lean
namespace SDCA.Smooth.SDFresh
open scoped InnerProductSpace

theorem wOf_mix {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (α β : Fin n → ℝ) (a b : ℝ) :
    wOf lam x (a • α+b • β) = a • wOf lam x α+b • wOf lam x β := by
  simp only [wOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  module

theorem gap_convex {d n : ℕ} (hn : 0 < n) (lam : ℝ) (hl : 0 ≤ lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (hc : ∀ i, ConvexOn ℝ Set.univ (φ i)) :
    ConvexOn ℝ {α | Feasible φ α} (gap lam x φ) := by
  refine ⟨feasible_convex φ, ?_⟩
  intro α hα β hβ a b ha hb hab
  have hp (i : Fin n) : φ i ⟪wOf lam x (a • α+b • β),x i⟫_ℝ ≤
      a*φ i ⟪wOf lam x α,x i⟫_ℝ+b*φ i ⟪wOf lam x β,x i⟫_ℝ := by
    simpa only [wOf_mix, inner_add_left, real_inner_smul_left, smul_eq_mul] using
      (hc i).2 (Set.mem_univ ⟪wOf lam x α,x i⟫_ℝ) (Set.mem_univ ⟪wOf lam x β,x i⟫_ℝ) ha hb hab
  have hq (i : Fin n) := (conjugate_convex φ i).2 hα hβ ha hb hab
  have hnorm : ‖wOf lam x (a • α+b • β)‖^2 ≤ a*‖wOf lam x α‖^2+b*‖wOf lam x β‖^2 := by
    rw [wOf_mix]
    exact (convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hp' := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun i _ => hp i)
    (show 0 ≤ 1/(n:ℝ) by positivity)
  have hq' := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun i _ => hq i)
    (show 0 ≤ 1/(n:ℝ) by positivity)
  have hn' := mul_le_mul_of_nonneg_left hnorm hl
  simp only [gap, primal, dualReal, Finset.sum_neg_distrib, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum] at hp' hq' ⊢
  linarith

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/AveragedGap.lean
namespace SDCA.Smooth.SDFresh

theorem alphaAvg_feasible_gap {d n T : ℕ} (hn : 0 < n) (lam : ℝ) (hl : 0 ≤ lam)
    (x : Fin n → EuclideanSpace ℝ (Fin d)) (φ : Fin n → ℝ → ℝ)
    (hc : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (js : Fin T → Fin n) (T₀ : ℕ) (hT : T₀ < T)
    (hf : ∀ t, Feasible φ (alphaIter Δ js t)) :
    Feasible φ (alphaAvg Δ js T₀) ∧
      gap lam x φ (alphaAvg Δ js T₀) ≤
        (1/((T:ℝ)-T₀))*∑ t ∈ Finset.Ico T₀ T, gap lam x φ (alphaIter Δ js t) := by
  have hp' : (0:ℝ) < (T:ℝ)-T₀ := by exact sub_pos.mpr (by exact_mod_cast hT)
  have hw : ∑ t ∈ Finset.Ico T₀ T, (1/((T:ℝ)-T₀)) = 1 := by
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [Nat.cast_sub hT.le]
    field_simp
  have he : (∑ t ∈ Finset.Ico T₀ T, (1/((T:ℝ)-T₀)) • alphaIter Δ js t) = alphaAvg Δ js T₀ := by
    simp only [alphaAvg, Finset.smul_sum]
  have hmem := (feasible_convex φ).sum_mem (fun _ _ => le_of_lt (one_div_pos.mpr hp')) hw
    (fun t _ => hf t)
  have hg := (gap_convex hn lam hl x φ hc).map_sum_le (fun _ _ => le_of_lt (one_div_pos.mpr hp')) hw
    (fun t _ => hf t)
  rw [he] at hmem hg
  refine ⟨hmem, ?_⟩
  simpa only [smul_eq_mul, Finset.mul_sum] using hg

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/NativeGap.lean
namespace SDCA.Smooth.SDFresh

theorem gap_eq_native {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) (hα : Feasible φ α) :
    gap lam x φ α = primal lam x φ (wOf lam x α)-(dual lam x φ α).toReal := by
  rw [← dualReal_coe lam x φ α hα]
  simp [gap]

theorem dual_ne_bot {d n : ℕ} (lam : ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (α : Fin n → ℝ) (hα : Feasible φ α) :
    dual lam x φ α ≠ ⊥ := by
  rw [← dualReal_coe lam x φ α hα]
  simp

end SDCA.Smooth.SDFresh

-- Complete module: SDProof/NativeConclusion.lean

namespace SDCA.Smooth.SDFresh

/-- Theorem 2, p. 6 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2). Run Procedure SDCA from `α⁽⁰⁾ = 0`
with convex `(1/γ)`-smooth losses `φᵢ` and the standing assumptions `‖xᵢ‖ ≤ 1`, `φᵢ ≥ 0`,
`φᵢ(0) ≤ 1` (p. 5), coordinates drawn i.i.d. uniformly. Let `εP > 0`. Then every dual value along
the run and at the outputs is finite, and:
1. if `T ≥ (n + 1/(λγ)) log((n + 1/(λγ)) · 1/εP)`, then `E[P(w⁽ᵀ⁾) − D(α⁽ᵀ⁾)] ≤ εP`;
2. if `T > T₀` and `T₀ ≥ (n + 1/(λγ)) log((n + 1/(λγ)) · 1/((T − T₀) εP))`, then the Averaging
   option output `ᾱ = (1/(T − T₀)) ∑_{t=T₀+1}^{T} α⁽ᵗ⁻¹⁾`, `w̄ = w(ᾱ)`, has `E[P(w̄) − D(ᾱ)] ≤ εP`;
3. under the same condition, the Random option output (the iterate `α⁽ᵗ⁻¹⁾` for `t` uniform on
   `{T₀+1, …, T}`, independent of the run) has `E[P(w̄) − D(ᾱ)] ≤ εP`. -/
theorem native_theorem_2 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ φ' : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ)
    (hderiv : ∀ i a, HasDerivAt (φ i) (φ' i a) a)
    (hsmooth : ∀ i a b, |φ' i a - φ' i b| ≤ (1 / γ) * |a - b|)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (εP : ℝ) (hεP : 0 < εP) :
    ((∀ (T : ℕ) (js : Fin T → Fin n) (t : ℕ), dual lam x φ (alphaIter Δ js t) ≠ ⊥) ∧
      ∀ (T : ℕ) (js : Fin T → Fin n) (T₀ : ℕ), T₀ < T → dual lam x φ (alphaAvg Δ js T₀) ≠ ⊥) ∧
    (∀ T : ℕ,
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / εP)) ≤ T →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaIter Δ js T)) -
            (dual lam x φ (alphaIter Δ js T)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaAvg Δ js T₀)) -
            (dual lam x φ (alphaAvg Δ js T₀)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      (1 / ((T : ℝ) - T₀)) * ∑ t ∈ Finset.Ico T₀ T,
          SAGA.Convex.expectIdx n T (fun js =>
            primal lam x φ (wOf lam x (alphaIter Δ js t)) -
              (dual lam x φ (alphaIter Δ js t)).toReal) ≤ εP) := by
  have hf (T : ℕ) (js : Fin T → Fin n) (t : ℕ) : Feasible φ (alphaIter Δ js t) :=
    alphaIter_invariant Δ (Feasible φ) (feasible_zero φ hφnn)
      (fun α hα i => feasible_step lam x φ Δ hΔ α hα i) js t
  have havg (T : ℕ) (js : Fin T → Fin n) (s : ℕ) (hst : s<T) :=
    alphaAvg_feasible_gap hn lam hlam.le x φ hconv Δ js s hst (hf T js)
  have hr := native_rates hn x φ φ' hconv lam γ hlam hγ hderiv hsmooth hx hφnn hφ0 Δ hΔ
  let c : ℝ := n+1/(lam*γ)
  have hc : 0<c := by dsimp [c]; positivity
  have hg (T : ℕ) (js : Fin T → Fin n) (t : ℕ) :=
    gap_eq_native lam x φ (alphaIter Δ js t) (hf T js t)
  have hw (s T : ℕ) (hst : s<T)
      (ht : c*Real.log (c*(1/(((T:ℝ)-s)*εP))) ≤ s) :
      (1/((T:ℝ)-s))*∑ t ∈ Finset.Ico s T,
        SAGA.Convex.expectIdx n T (fun js => gap lam x φ (alphaIter Δ js t)) ≤ εP := by
    have hpos : 0<(T:ℝ)-s := by
      have hcast : (s:ℝ)<T := by exact_mod_cast hst
      linarith
    exact (hr.2 s T hst).trans (log_window_bound hc hεP hpos (by simpa [c, div_eq_mul_inv] using ht))
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro T js t
    exact dual_ne_bot lam x φ _ (hf T js t)
  · intro T js s hst
    exact dual_ne_bot lam x φ _ (havg T js s hst).1
  · intro T ht
    have h := (hr.1 T).trans (log_rate_bound hc hεP (by simpa [c, div_eq_mul_inv] using ht))
    simpa only [runMean, hg] using h
  · intro s T hst ht
    have hm := expectIdx_mono (T := T) (fun js => (havg T js s hst).2)
    rw [expectIdx_mul, expectIdx_finset_sum] at hm
    have hb := hm.trans (hw s T hst ht)
    have hga (js : Fin T → Fin n) :=
      gap_eq_native lam x φ (alphaAvg Δ js s) (havg T js s hst).1
    simpa only [hga] using hb
  · intro s T hst ht
    have h := hw s T hst ht
    simpa only [hg] using h


end SDCA.Smooth.SDFresh

-- Complete module: SDProof/FinalRoot.lean
namespace SDCA.Smooth

/-- Theorem 2, p. 6 (Shalev-Shwartz–Zhang, arXiv:1209.1873v2). Run Procedure SDCA from `α⁽⁰⁾ = 0`
with convex `(1/γ)`-smooth losses `φᵢ` and the standing assumptions `‖xᵢ‖ ≤ 1`, `φᵢ ≥ 0`,
`φᵢ(0) ≤ 1` (p. 5), coordinates drawn i.i.d. uniformly. Let `εP > 0`. Then every dual value along
the run and at the outputs is finite, and:
1. if `T ≥ (n + 1/(λγ)) log((n + 1/(λγ)) · 1/εP)`, then `E[P(w⁽ᵀ⁾) − D(α⁽ᵀ⁾)] ≤ εP`;
2. if `T > T₀` and `T₀ ≥ (n + 1/(λγ)) log((n + 1/(λγ)) · 1/((T − T₀) εP))`, then the Averaging
   option output `ᾱ = (1/(T − T₀)) ∑_{t=T₀+1}^{T} α⁽ᵗ⁻¹⁾`, `w̄ = w(ᾱ)`, has `E[P(w̄) − D(ᾱ)] ≤ εP`;
3. under the same condition, the Random option output (the iterate `α⁽ᵗ⁻¹⁾` for `t` uniform on
   `{T₀+1, …, T}`, independent of the run) has `E[P(w̄) − D(ᾱ)] ≤ εP`. -/
theorem theorem_2 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ φ' : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ)
    (hderiv : ∀ i a, HasDerivAt (φ i) (φ' i a) a)
    (hsmooth : ∀ i a b, |φ' i a - φ' i b| ≤ (1 / γ) * |a - b|)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (εP : ℝ) (hεP : 0 < εP) :
    ((∀ (T : ℕ) (js : Fin T → Fin n) (t : ℕ), dual lam x φ (alphaIter Δ js t) ≠ ⊥) ∧
      ∀ (T : ℕ) (js : Fin T → Fin n) (T₀ : ℕ), T₀ < T → dual lam x φ (alphaAvg Δ js T₀) ≠ ⊥) ∧
    (∀ T : ℕ,
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / εP)) ≤ T →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaIter Δ js T)) -
            (dual lam x φ (alphaIter Δ js T)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaAvg Δ js T₀)) -
            (dual lam x φ (alphaAvg Δ js T₀)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      (1 / ((T : ℝ) - T₀)) * ∑ t ∈ Finset.Ico T₀ T,
          SAGA.Convex.expectIdx n T (fun js =>
            primal lam x φ (wOf lam x (alphaIter Δ js t)) -
              (dual lam x φ (alphaIter Δ js t)).toReal) ≤ εP) := by
  exact SDFresh.native_theorem_2 hn x φ φ' hconv lam γ hlam hγ hderiv hsmooth hx hφnn hφ0 Δ hΔ εP hεP

end SDCA.Smooth


open SDCA.Smooth
open scoped BigOperators
theorem solution {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ φ' : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam γ : ℝ) (hlam : 0 < lam) (hγ : 0 < γ)
    (hderiv : ∀ i a, HasDerivAt (φ i) (φ' i a) a)
    (hsmooth : ∀ i a b, |φ' i a - φ' i b| ≤ (1 / γ) * |a - b|)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hφnn : ∀ i a, 0 ≤ φ i a) (hφ0 : ∀ i, φ i 0 ≤ 1)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (εP : ℝ) (hεP : 0 < εP) :
    ((∀ (T : ℕ) (js : Fin T → Fin n) (t : ℕ), dual lam x φ (alphaIter Δ js t) ≠ ⊥) ∧
      ∀ (T : ℕ) (js : Fin T → Fin n) (T₀ : ℕ), T₀ < T → dual lam x φ (alphaAvg Δ js T₀) ≠ ⊥) ∧
    (∀ T : ℕ,
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / εP)) ≤ T →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaIter Δ js T)) -
            (dual lam x φ (alphaIter Δ js T)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      SAGA.Convex.expectIdx n T (fun js =>
          primal lam x φ (wOf lam x (alphaAvg Δ js T₀)) -
            (dual lam x φ (alphaAvg Δ js T₀)).toReal) ≤ εP) ∧
    (∀ T₀ T : ℕ, T₀ < T →
      (n + 1 / (lam * γ)) * Real.log ((n + 1 / (lam * γ)) * (1 / (((T : ℝ) - T₀) * εP))) ≤ T₀ →
      (1 / ((T : ℝ) - T₀)) * ∑ t ∈ Finset.Ico T₀ T,
          SAGA.Convex.expectIdx n T (fun js =>
            primal lam x φ (wOf lam x (alphaIter Δ js t)) -
              (dual lam x φ (alphaIter Δ js t)).toReal) ≤ εP) := by
  exact SDCA.Smooth.theorem_2 hn x φ φ' hconv lam γ hlam hγ hderiv hsmooth hx hφnn hφ0 Δ hΔ εP hεP
