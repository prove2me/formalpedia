-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.Supplement.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:03.207466+00:00
-- url     : https://prove2.me/submissions/a3c09842-b3ab-4b89-bb93-a5f443844173

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Barrier
import Definitions.Def_ProjSelfConcordant_ConicExt_Supplement_Duality

open ProjSelfConcordant
open ProjSelfConcordant.ConicExt
open ProjSelfConcordant.ConicExt.Supplement

/-- Lemma 5.3, p. 13: let `f` be a projectively self-concordant function on a regular convex set
`X`, let `f∗` be defined at `p`, and let `x∗ ∈ Xᵒ` be a critical point of
`q_p(x) = f(x) + log(1 + ⟨x, p⟩)`. Then `x∗` is the unique critical point of `q_p` in `Xᵒ`, a global
minimizer of `q_p` on `Xᵒ`, `q_p″(x∗) ≻ 0`, and at `x = x∗`:
`f′(x) = −p/(1 + ⟨x, p⟩)`, `p = −f′(x)/(1 + ⟨f′(x), x⟩)`, `1 + ⟨f′(x), x⟩ = 1/(1 + ⟨x, p⟩) > 0`. -/
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : RegularConvexSet X) (γ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ProjSCFun γ X f) (p : EuclideanSpace ℝ (Fin n)) (hp : p ∈ dualDomain X f)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ interior X)
    (hcrit : fderiv ℝ (qfun f p) xs = 0) :
    (∀ y ∈ interior X, fderiv ℝ (qfun f p) y = 0 → y = xs) ∧
    (∀ y ∈ interior X, qfun f p xs ≤ qfun f p y) ∧
    (∀ h : EuclideanSpace ℝ (Fin n), h ≠ 0 → 0 < d2 (qfun f p) xs h h) ∧
    gradient f xs = -(1 + inner ℝ xs p)⁻¹ • p ∧
    p = -(1 + inner ℝ (gradient f xs) xs)⁻¹ • gradient f xs ∧
    1 + inner ℝ (gradient f xs) xs = (1 + inner ℝ xs p)⁻¹ ∧
    0 < (1 + inner ℝ xs p)⁻¹ := by
      have hD : IsOpen (interior X) := isOpen_interior
      have hDc : Convex ℝ (interior X) := hX.2.1.interior
      have hfC : ∀ a ∈ interior X, ContDiffAt ℝ 3 f a := fun a ha =>
        hf.2.1.contDiffAt (hD.mem_nhds ha)
      have hfd : ∀ a ∈ interior X, HasFDerivAt f (fderiv ℝ f a) a := fun a ha =>
        ((hfC a ha).differentiableAt (by norm_num)).hasFDerivAt
      have hfdd : ∀ a ∈ interior X,
          HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) a) a := fun a ha =>
        (((hfC a ha).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
      have hℓ : ∀ a ∈ interior X, 0 < 1 + inner ℝ a p := hp.1
      have hℓfd : ∀ a, HasFDerivAt (fun x => 1 + inner ℝ x p) (innerSL ℝ p) a := by
        intro a
        have : (fun x : EuclideanSpace ℝ (Fin n) => 1 + inner ℝ x p)
            = fun x => 1 + innerSL ℝ p x := by
          funext x; simp [real_inner_comm]
        rw [this]
        exact ((innerSL ℝ p).hasFDerivAt).const_add 1
      have hq : ∀ a ∈ interior X, HasFDerivAt (qfun f p)
          (fderiv ℝ f a + (1 + inner ℝ a p)⁻¹ • innerSL ℝ p) a := by
        intro a ha
        exact (hfd a ha).add ((hℓfd a).log (hℓ a ha).ne')
      have hcritf : ∀ a ∈ interior X, fderiv ℝ (qfun f p) a = 0 →
          ∀ h, fderiv ℝ f a h = -(1 + inner ℝ a p)⁻¹ * inner ℝ h p := by
        intro a ha hc h
        have h1 := congrArg (fun L => L h) ((hq a ha).fderiv.symm.trans hc)
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          innerSL_apply_apply, ContinuousLinearMap.zero_apply, smul_eq_mul] at h1
        have e1 : inner ℝ p a = inner ℝ a p := real_inner_comm a p
        have e2 : inner ℝ p h = inner ℝ h p := real_inner_comm h p
        erw [e2] at h1
        linarith
      have hcond1 : ∀ a ∈ interior X, ∀ h, h ≠ 0 →
          0 < fderiv ℝ (fderiv ℝ f) a h h - (fderiv ℝ f a h) ^ 2 := by
        intro a ha h hh
        have := hf.2.2.1 a ha h hh
        unfold dk at this
        rwa [iteratedFDeriv_two_apply, iteratedFDeriv_one_apply] at this
      have key : ∀ a ∈ interior X, fderiv ℝ (qfun f p) a = 0 →
          ∀ y ∈ interior X, y ≠ a → qfun f p a < qfun f p y := by
        intro a ha hca y hy hya
        set d := y - a with hd
        have hd0 : d ≠ 0 := sub_ne_zero.mpr hya
        set ℓa := 1 + inner ℝ a p with hℓa_def
        have hℓa : 0 < ℓa := hℓ a ha
        set c := Real.exp (-f a) / ℓa with hc
        let z : ℝ → EuclideanSpace ℝ (Fin n) := fun t => a + t • d
        have hz : ∀ t ∈ Set.Icc (0:ℝ) 1, z t ∈ interior X := fun t ht =>
          hDc.add_smul_sub_mem ha hy ht
        have hzd : ∀ t, HasDerivAt z d t := by
          intro t
          have := ((hasDerivAt_id t).smul_const d).const_add a
          simp only [id, one_smul] at this
          exact this
        let ψ : ℝ → ℝ := fun t => Real.exp (-f (z t)) - c * (1 + inner ℝ (z t) p)
        let ψ1 : ℝ → ℝ := fun t =>
          -(Real.exp (-f (z t)) * fderiv ℝ f (z t) d) - c * inner ℝ d p
        let ψ2 : ℝ → ℝ := fun t =>
          Real.exp (-f (z t)) * (fderiv ℝ f (z t) d) ^ 2
            - Real.exp (-f (z t)) * fderiv ℝ (fderiv ℝ f) (z t) d d
        have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (ψ1 t) t := by
          intro t ht
          have h1 : HasDerivAt (fun t => f (z t)) (fderiv ℝ f (z t) d) t :=
            (hfd (z t) (hz t ht)).comp_hasDerivAt t (hzd t)
          have h2 := h1.neg.exp
          have h3 : HasDerivAt (fun t => inner ℝ (z t) p) (inner ℝ d p) t := by
            have := (hzd t).inner ℝ (hasDerivAt_const t p)
            simpa using this
          have h4 := h2.sub ((h3.const_add 1).const_mul c)
          exact h4.congr_deriv (by simp only [ψ1, Pi.neg_apply]; ring)
        have hψ1 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ1 (ψ2 t) t := by
          intro t ht
          have h1 : HasDerivAt (fun t => f (z t)) (fderiv ℝ f (z t) d) t :=
            (hfd (z t) (hz t ht)).comp_hasDerivAt t (hzd t)
          have h2 := h1.neg.exp
          have h5 : HasDerivAt (fun t => fderiv ℝ f (z t))
              (fderiv ℝ (fderiv ℝ f) (z t) d) t :=
            (hfdd (z t) (hz t ht)).comp_hasDerivAt t (hzd t)
          have h6 := h5.clm_apply (hasDerivAt_const t d)
          have h7 := ((h2.mul h6).neg).sub_const (c * inner ℝ d p)
          exact h7.congr_deriv (by simp only [ψ2, Pi.neg_apply, map_zero, add_zero]; ring)
        have hψ2 : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ2 t < 0 := by
          intro t ht
          have := hcond1 (z t) (hz t ht) d hd0
          have he := Real.exp_pos (-f (z t))
          simp only [ψ2]
          nlinarith
        have hψ1_0 : ψ1 0 = 0 := by
          have hz0 : z 0 = a := by simp [z]
          simp only [ψ1, hz0]
          rw [hcritf a ha hca d, hc, ← hℓa_def]
          field_simp
          ring
        have hanti1 : StrictAntiOn ψ1 (Set.Icc 0 1) := by
          apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
          · intro t ht; exact (hψ1 t ht).continuousAt.continuousWithinAt
          · intro t ht
            rw [interior_Icc] at ht
            rw [(hψ1 t (Set.Ioo_subset_Icc_self ht)).deriv]
            exact hψ2 t (Set.Ioo_subset_Icc_self ht)
        have hanti : StrictAntiOn ψ (Set.Icc 0 1) := by
          apply strictAntiOn_of_deriv_neg (convex_Icc 0 1)
          · intro t ht; exact (hψ t ht).continuousAt.continuousWithinAt
          · intro t ht
            rw [interior_Icc] at ht
            rw [(hψ t (Set.Ioo_subset_Icc_self ht)).deriv, ← hψ1_0]
            exact hanti1 (Set.left_mem_Icc.mpr zero_le_one) (Set.Ioo_subset_Icc_self ht) ht.1
        have hlt : ψ 1 < ψ 0 :=
          hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_lt_one
        have hz0 : z 0 = a := by simp [z]
        have hz1 : z 1 = y := by simp [z, d]
        simp only [ψ, hz0, hz1] at hlt
        have hℓy : 0 < 1 + inner ℝ y p := hℓ y hy
        rw [← Real.exp_lt_exp]
        unfold qfun
        rw [Real.exp_add, Real.exp_add, Real.exp_log hℓa, Real.exp_log hℓy]
        rw [hc, Real.exp_neg, Real.exp_neg] at hlt
        have hA := Real.exp_pos (f a)
        have hB := Real.exp_pos (f y)
        rw [← hℓa_def] at hlt
        have e1 : (Real.exp (f a))⁻¹ / ℓa * ℓa = (Real.exp (f a))⁻¹ := by field_simp
        rw [e1] at hlt
        have h0 : (Real.exp (f y))⁻¹ < (Real.exp (f a))⁻¹ / ℓa * (1 + inner ℝ y p) := by linarith
        have h1 := mul_lt_mul_of_pos_left h0 (mul_pos (mul_pos hA hℓa) hB)
        have e2 : Real.exp (f a) * ℓa * Real.exp (f y) * (Real.exp (f y))⁻¹ = Real.exp (f a) * ℓa := by
          field_simp
        have e3 : Real.exp (f a) * ℓa * Real.exp (f y) * ((Real.exp (f a))⁻¹ / ℓa * (1 + inner ℝ y p))
            = Real.exp (f y) * (1 + inner ℝ y p) := by
          field_simp
        rw [e2, e3] at h1
        exact h1
      have hℓx := hℓ xs hxs
      have hfx := hcritf xs hxs hcrit
      have hgrad : gradient f xs = -(1 + inner ℝ xs p)⁻¹ • p := by
        apply ext_inner_right ℝ
        intro v
        rw [gradient, InnerProductSpace.toDual_symm_apply, hfx v, real_inner_smul_left,
          real_inner_comm v p]
      have h6 : 1 + inner ℝ (gradient f xs) xs = (1 + inner ℝ xs p)⁻¹ := by
        rw [hgrad, real_inner_smul_left, real_inner_comm xs p]
        field_simp
        ring
      refine ⟨?_, ?_, ?_, hgrad, ?_, h6, inv_pos.mpr hℓx⟩
      · intro y hy hyc
        by_contra hne
        have h1 := key xs hxs hcrit y hy hne
        have h2 := key y hy hyc xs hxs (Ne.symm hne)
        linarith
      · intro y hy
        by_cases hyx : y = xs
        · rw [hyx]
        · exact le_of_lt (key xs hxs hcrit y hy hyx)
      · intro h hh
        unfold d2
        rw [iteratedFDeriv_two_apply]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        have heq : fderiv ℝ (qfun f p) =ᶠ[nhds xs]
            fun y => fderiv ℝ f y + (1 + inner ℝ y p)⁻¹ • innerSL ℝ p :=
          Filter.eventually_of_mem (hD.mem_nhds hxs) (fun y hy => (hq y hy).fderiv)
        rw [heq.fderiv_eq]
        have hinv : HasFDerivAt (fun y => (1 + inner ℝ y p)⁻¹)
            ((-((1 + inner ℝ xs p) ^ 2)⁻¹) • innerSL ℝ p) xs :=
          (hasDerivAt_inv hℓx.ne').comp_hasFDerivAt xs (hℓfd xs)
        have hG : HasFDerivAt (fun y => fderiv ℝ f y + (1 + inner ℝ y p)⁻¹ • innerSL ℝ p)
            (fderiv ℝ (fderiv ℝ f) xs
              + ((-((1 + inner ℝ xs p) ^ 2)⁻¹) • innerSL ℝ p).smulRight (innerSL ℝ p)) xs :=
          (hfdd xs hxs).add (hinv.smul_const (innerSL ℝ p))
        rw [hG.fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
        have hc1 := hcond1 xs hxs h hh
        have e : -((1 + inner ℝ xs p) ^ 2)⁻¹ * inner ℝ p h * inner ℝ p h
            = -(fderiv ℝ f xs h) ^ 2 := by
          rw [hfx h, real_inner_comm h p]
          field_simp
        linarith
      · rw [h6, inv_inv, hgrad, smul_smul, neg_mul_neg, mul_inv_cancel₀ hℓx.ne', one_smul]
