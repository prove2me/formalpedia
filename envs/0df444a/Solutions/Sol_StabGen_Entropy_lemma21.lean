-- Prove2me | solution 1 for StabGen.Entropy.lemma21
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:18:15.921488+00:00
-- url     : https://prove2.me/submissions/69214709-5602-499b-8ff0-52357480ed0e

import Mathlib
import Definitions.Def_StabGen_Entropy_GeneralRegularization

set_option autoImplicit false

namespace F6fa8af8Aux

theorem breg_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ℝ)
    (hF : ConvexOn ℝ Set.univ F) (x y : E) (hd : DifferentiableAt ℝ F x) :
    fderiv ℝ F x (y - x) ≤ F y - F x := by
  have hg : ConvexOn ℝ Set.univ (F ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)) := by
    have := hF.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)
    simpa using this
  have hder : HasDerivAt (F ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E)) (fderiv ℝ F x (y - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x y : ℝ → E) (y - x) 0 :=
      AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt F (fderiv ℝ F x) (AffineMap.lineMap x y (0:ℝ)) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hder
  simpa [slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using this

theorem deriv_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → ℝ) (x v : E)
    (hd : DifferentiableAt ℝ G x) (C : ℝ) (hC : 0 ≤ C)
    (hlip : ∀ t : ℝ, |G (x + t • v) - G x| ≤ C * |t|) : |fderiv ℝ G x v| ≤ C := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have h2 : HasFDerivAt G (fderiv ℝ G x) ((fun t : ℝ => x + t • v) 0) := by
    simpa using hd.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0:ℝ) h1
  have h4 := h3.hasFDerivAt.le_of_lip' hC (Filter.Eventually.of_forall fun t => by
    simpa [Real.norm_eq_abs] using hlip t)
  have h5 := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (fderiv ℝ G x v)).le_opNorm 1
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul,
    norm_one, mul_one, Real.norm_eq_abs] at h5
  exact h5.trans h4

theorem convex_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) (L : ι → E → ℝ) (hL : ∀ j, ConvexOn ℝ Set.univ (L j)) :
    ConvexOn ℝ Set.univ (fun g => ∑ j ∈ s, L j g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (convexOn_const (0:ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
  | insert a s ha ih =>
    show ConvexOn ℝ Set.univ (fun g => ∑ j ∈ insert a s, L j g)
    simp only [Finset.sum_insert ha]
    exact (hL a).add ih

end F6fa8af8Aux

open StabGen.Entropy FoundationsML.Stability in
theorem solution {X Y E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (ev : E →ₗ[ℝ] (X → ℝ)) (c : ℝ → Y → ℝ) (σ lam : ℝ) (N : E → ℝ)
    (S : Fin m → X × Y) (i : Fin m) (f f' : E)
    (hσ : StabGen.RKHS.SigmaAdmissible (Set.range ev) c σ) (hlam : 0 < lam)
    (hN : ConvexOn ℝ Set.univ N) (hNd : Differentiable ℝ N)
    (hℓd : ∀ z : X × Y, Differentiable ℝ (fun g : E => Loss c (ev g) z))
    (hmin : ∀ g : E, StabGen.RKHS.regRisk c ev S lam N f ≤ StabGen.RKHS.regRisk c ev S lam N g)
    (hmin' : ∀ g : E, StabGen.RKHS.truncRegRisk c ev S i lam N f' ≤ StabGen.RKHS.truncRegRisk c ev S i lam N g) :
    bregmanDiv N f f' + bregmanDiv N f' f ≤
        (1 / (lam * (m : ℝ))) *
          (Loss c (ev f') (S i) - Loss c (ev f) (S i) -
            bregmanDiv (fun g : E => Loss c (ev g) (S i)) f' f) ∧
      (1 / (lam * (m : ℝ))) *
          (Loss c (ev f') (S i) - Loss c (ev f) (S i) -
            bregmanDiv (fun g : E => Loss c (ev g) (S i)) f' f) ≤
        (σ / (lam * (m : ℝ))) * |ev (f' - f) (S i).1| := by
  classical
  have hm : (0:ℝ) < m := by exact_mod_cast i.pos
  set ℓ : E → ℝ := fun g => Loss c (ev g) (S i) with hℓ
  set P : E → ℝ := fun g => (1 / (m:ℝ)) * ∑ j ∈ Finset.univ.erase i, Loss c (ev g) (S j) with hP
  have hR : StabGen.RKHS.regRisk c ev S lam N = fun g => (P g + (1/(m:ℝ)) * ℓ g) + lam * N g := by
    funext g
    simp only [StabGen.RKHS.regRisk, EmpiricalError, hP, hℓ]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
  have hR' : StabGen.RKHS.truncRegRisk c ev S i lam N = fun g => P g + lam * N g := by
    funext g; simp only [StabGen.RKHS.truncRegRisk, hP]
  have hPd : Differentiable ℝ P := by
    intro g
    show DifferentiableAt ℝ (fun g => (1 / (m:ℝ)) * ∑ j ∈ Finset.univ.erase i, Loss c (ev g) (S j)) g
    exact (DifferentiableAt.fun_sum (u := Finset.univ.erase i)
      (A := fun j g => Loss c (ev g) (S j)) fun j _ => hℓd (S j) g).const_mul _
  have hℓdi : Differentiable ℝ ℓ := hℓd (S i)
  have hPc : ConvexOn ℝ Set.univ P := by
    have hj : ∀ j, ConvexOn ℝ Set.univ (fun g : E => Loss c (ev g) (S j)) := by
      intro j
      have := (hσ.2.1 (S j).2).comp_linearMap ((LinearMap.proj (S j).1).comp ev)
      simpa [Function.comp_def, Loss] using this
    have := (F6fa8af8Aux.convex_sum (Finset.univ.erase i) _ hj).smul
      (show (0:ℝ) ≤ 1 / (m:ℝ) by positivity)
    simpa [hP, smul_eq_mul] using this
  -- first-order conditions
  have hF1 : HasFDerivAt (StabGen.RKHS.regRisk c ev S lam N)
      ((fderiv ℝ P f + (1/(m:ℝ)) • fderiv ℝ ℓ f) + lam • fderiv ℝ N f) f := by
    rw [hR]
    exact ((hPd f).hasFDerivAt.add ((hℓdi f).hasFDerivAt.const_mul _)).add
      ((hNd f).hasFDerivAt.const_mul _)
  have hF2 : HasFDerivAt (StabGen.RKHS.truncRegRisk c ev S i lam N)
      (fderiv ℝ P f' + lam • fderiv ℝ N f') f' := by
    rw [hR']
    exact (hPd f').hasFDerivAt.add ((hNd f').hasFDerivAt.const_mul _)
  have hz1 := (IsLocalMin.hasFDerivAt_eq_zero
    (Filter.Eventually.of_forall hmin : IsLocalMin _ f) hF1)
  have hz2 := (IsLocalMin.hasFDerivAt_eq_zero
    (Filter.Eventually.of_forall hmin' : IsLocalMin _ f') hF2)
  have e1 := congrArg (fun L => L (f' - f)) hz1
  have e2 := congrArg (fun L => L (f - f')) hz2
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.zero_apply] at e1 e2
  have c1 := F6fa8af8Aux.breg_nonneg P hPc f f' (hPd f)
  have c2 := F6fa8af8Aux.breg_nonneg P hPc f' f (hPd f')
  -- derivative bound
  have hb : |fderiv ℝ ℓ f (f' - f)| ≤ σ * |ev (f' - f) (S i).1| := by
    apply F6fa8af8Aux.deriv_bound ℓ f (f' - f) (hℓdi f) _ (mul_nonneg hσ.1 (abs_nonneg _))
    intro t
    have := hσ.2.2 (ev (f + t • (f' - f)) (S i).1) ⟨ev (f + t • (f' - f)), ⟨_, rfl⟩, (S i).1, rfl⟩
      (ev f (S i).1) ⟨ev f, ⟨_, rfl⟩, (S i).1, rfl⟩ (S i).2
    simp only [hℓ, Loss]
    convert this using 1
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      abs_mul]
    ring
  have hb' := (abs_le.mp hb).2
  simp only [bregmanDiv]
  have key : Loss c (ev f') (S i) - Loss c (ev f) (S i) -
      (Loss c (ev f') (S i) - Loss c (ev f) (S i) - fderiv ℝ (fun g : E => Loss c (ev g) (S i)) f (f' - f))
      = fderiv ℝ ℓ f (f' - f) := by simp only [hℓ]; ring
  rw [key]
  have hlm : 0 < lam * (m:ℝ) := mul_pos hlam hm
  have hfN : fderiv ℝ N f' (f - f') = - fderiv ℝ N f' (f' - f) := by
    rw [← map_neg, neg_sub]
  constructor
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlm]
    have hsum : fderiv ℝ P f (f' - f) + fderiv ℝ P f' (f - f') ≤ 0 := by linarith
    have h1 : lam * (fderiv ℝ N f (f' - f) + fderiv ℝ N f' (f - f')) =
        -(fderiv ℝ P f (f' - f) + fderiv ℝ P f' (f - f')) - (1 / (m:ℝ)) * fderiv ℝ ℓ f (f' - f) := by
      linarith
    calc (N f - N f' - fderiv ℝ N f' (f - f') + (N f' - N f - fderiv ℝ N f (f' - f))) * (lam * m)
        = -(lam * (fderiv ℝ N f (f' - f) + fderiv ℝ N f' (f - f'))) * m := by ring
      _ = (fderiv ℝ P f (f' - f) + fderiv ℝ P f' (f - f')) * m
            + ((1 / (m:ℝ)) * m) * fderiv ℝ ℓ f (f' - f) := by rw [h1]; ring
      _ = (fderiv ℝ P f (f' - f) + fderiv ℝ P f' (f - f')) * m + fderiv ℝ ℓ f (f' - f) := by
            rw [one_div, inv_mul_cancel₀ hm.ne', one_mul]
      _ ≤ fderiv ℝ ℓ f (f' - f) := by nlinarith
  · rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hb' hlm.le
