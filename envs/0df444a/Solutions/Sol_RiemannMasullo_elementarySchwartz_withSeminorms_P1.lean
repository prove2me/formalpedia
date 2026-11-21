-- Prove2me | solution 1 for RiemannMasullo.elementarySchwartz_withSeminorms_P1
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:38:17.102402+00:00
-- url     : https://prove2.me/submissions/bfca0c9e-9550-4c84-9041-d8683cc696b5

-- New proof of an upstream statement in mccorvie/riemann-masullo.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L449-L456
import Theorems.Thm_RiemannMasullo_elementarySchwartz_radial_weight_continuous_seminorm
import Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms
import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal
open Filter Topology
theorem solution :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            ‖elementaryPartial f i.2.2.1 i.2.2.2 xt a b‖) := by
  classical
  let I := ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)
  choose Q hc hv using (fun i : I => elementarySchwartz_radial_weight_continuous_seminorm (F:=F) (r:=r) i.1 i.2.1 i.2.2.1 i.2.2.2)
  refine ⟨Q, ?_, hv⟩
  let P : SeminormFamily ℂ (ElementarySchwartz m n r F) _ := elementarySchwartzSeminorm
  have hp : WithSeminorms P := elementarySchwartz_withSeminorms
  have hmono {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (v : Fin d → ℕ) :
      ‖∏ k,(x k : ℂ)^v k‖ ≤ 1+‖x‖^(∑ k,v k) := by
    rw [norm_prod,Finset.prod_congr rfl (fun k _ => norm_pow (x k : ℂ) _)]
    have h : ∏ k,‖(x k : ℂ)‖^(v k) ≤ ∏ k : Fin d, ‖x‖^(v k) :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun k _ =>
        pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Complex.norm_real] using PiLp.norm_apply_le x k) _)
    rw [←Finset.prod_pow_eq_pow_sum] 
    linarith
  have hdom (i : ElementarySchwartzIndex m n r) :
      ∃ j : I, ∀ f, P i f ≤ Q j f := by
    let j : I := (∑ k,i.1 k,∑ k,i.2.2.2 k,i.2.1,i.2.2.1)
    refine ⟨j,?_⟩
    intro f
    have h : elementarySchwartzBound f.val i ≤ ENNReal.ofReal (Q j f) := by
      rw [hv]
      apply iSup_le
      intro x
      apply iSup_le
      intro a
      apply iSup_le
      intro b
      apply le_iSup_of_le x
      apply le_iSup_of_le a
      apply le_iSup_of_le b
      change ‖((∏ k,(x.1 k : ℂ)^i.1 k)*(∏ k,(a k : ℂ)^i.2.2.2 k)) *
        elementaryPartial f i.2.1 i.2.2.1 x a b‖ₑ ≤ _
      rw [←ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      simp only [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      let y : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun k => (a k:ℝ))
      have ha := hmono y i.2.2.2
      simp only [y,WithLp.ofLp_toLp,Complex.ofReal_intCast] at ha
      exact mul_le_mul (hmono x.1 i.1) ha (norm_nonneg _) (by positivity)
    change (elementarySchwartzBound f.val i).toReal ≤ Q j f
    simpa only [ENNReal.toReal_ofReal (apply_nonneg _ _)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  apply (SeminormFamily.withSeminorms_iff_nhds_eq_iInf Q).mpr
  apply le_antisymm
  · apply le_iInf
    intro j
    apply Filter.tendsto_iff_comap.mp
    exact (hc j).tendsto' 0 0 (map_zero _)
  · rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf P).mp hp]
    apply le_iInf
    intro i
    obtain ⟨j,hj⟩ := hdom i
    apply le_trans (iInf_le _ j)
    apply Filter.tendsto_iff_comap.mp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (Filter.tendsto_comap : Filter.Tendsto (Q j) (Filter.comap (Q j) (𝓝 0)) (𝓝 0))
      (fun f => apply_nonneg (P i) f) hj
