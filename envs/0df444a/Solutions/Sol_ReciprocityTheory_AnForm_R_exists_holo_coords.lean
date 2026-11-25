-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_holo_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:34:54.375972+00:00
-- url     : https://prove2.me/submissions/19c928b2-e923-42a2-8616-7778ce3adc7a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChartA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Theorems.Thm_ReciprocityTheory_AnForm_R_analyticOnNhd_eval_univ
import Theorems.Thm_ReciprocityTheory_AnForm_R_eq_zero_of_grad
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_jacobian_cut
import Theorems.Thm_ReciprocityTheory_AnForm_hasFDerivAt_mvPolynomial_eval
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (e : ℕ)
    [IsRegularLocalRing (locRing K p)] (he : ringKrullDim (locRing K p) = e)
    (r : Fin e → MvPolynomial (Fin n) ℂ)
    (hr : Ideal.span (Set.range fun i => algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p) (r i)) =
      Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locRing K p)) (ptIdeal p)) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → (Fin n → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V (U ∩ zeroSet K) ∧ ∀ w ∈ V, evalFam r (g w) = w := by
  classical
  obtain ⟨hen, F, hFK, -, hh, hhp, hcut⟩ := exists_jacobian_cut K p e he
  let Ψ : (Fin n → ℂ) → (Fin e → ℂ) × (Fin (n - e) → ℂ) :=
    fun y => (evalFam r y, fun k => eval y (F k))
  have hΨ : ∀ y, Ψ y = (evalFam r y, fun k => eval y (F k)) := fun y => rfl
  let Lr : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) := ContinuousLinearMap.pi fun i =>
    ∑ j, eval p (pderiv j (r i)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j
  let LF : (Fin n → ℂ) →L[ℂ] (Fin (n - e) → ℂ) := ContinuousLinearMap.pi fun k =>
    ∑ j, eval p (pderiv j (F k)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j
  let Lm : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ) := Lr.prod LF
  have hΨd : HasFDerivAt Ψ Lm p :=
    (hasFDerivAt_pi.2 fun i => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (r i) p).prodMk
      (hasFDerivAt_pi.2 fun k => ReciprocityTheory.AnForm.hasFDerivAt_mvPolynomial_eval (F k) p)
  have hΨan : AnalyticAt ℂ Ψ p := by
    refine AnalyticAt.prod ?_ ?_
    · rw [analyticAt_pi_iff]; intro i; exact analyticOnNhd_eval_univ (r i) p (Set.mem_univ _)
    · rw [analyticAt_pi_iff]; intro k; exact analyticOnNhd_eval_univ (F k) p (Set.mem_univ _)
  have hstrict : HasStrictFDerivAt Ψ Lm p := by
    have := hΨan.hasStrictFDerivAt; rwa [hΨd.fderiv] at this
  have hinj : Function.Injective Lm := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    refine eq_zero_of_grad K p r hr F hFK hh hhp hcut v (fun i => ?_) (fun k => ?_)
    · have := congrFun (congrArg Prod.fst hv) i; simpa [Lm, Lr] using this
    · have := congrFun (congrArg Prod.snd hv) k; simpa [Lm, LF] using this
  have hsurjL : Function.Surjective Lm := by
    have hdim : Module.finrank ℂ (Fin n → ℂ) =
        Module.finrank ℂ ((Fin e → ℂ) × (Fin (n - e) → ℂ)) := by
      simp [Module.finrank_prod]; omega
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (Lm : (Fin n → ℂ) →ₗ[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective Lm (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurjL)
  have hLe : (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) = Lm :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hφ : HasStrictFDerivAt Ψ (Le : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin (n - e) → ℂ)) p := by
    rw [hLe]; exact hstrict
  let Φ := hφ.toOpenPartialHomeomorph Ψ
  have hΦ : ∀ x, Φ x = Ψ x := fun x => rfl
  have hpS : p ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt ℂ Φ.symm (Φ p) :=
    Φ.analyticAt_symm' (i := Le) hpS hΨan hφ.hasFDerivAt.fderiv
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T0, hT0s, hT0o, hT0p⟩ := mem_nhds_iff.mp hs
  have hHo : IsOpen {y : Fin n → ℂ | eval y hh ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval hh) continuous_const
  set O : Set (Fin n → ℂ) := (Φ.source ∩ {y | eval y hh ≠ 0}) ∩ Φ ⁻¹' T0 with hOdef
  have hO : IsOpen O := (Φ.continuousOn.mono Set.inter_subset_left).isOpen_inter_preimage
    (Φ.open_source.inter hHo) hT0o
  set T : Set ((Fin e → ℂ) × (Fin (n - e) → ℂ)) := Φ.target ∩ Φ.symm ⁻¹' O with hTdef
  have hT : IsOpen T := Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hO

  have hzs : ∀ y, eval y hh ≠ 0 → (∀ k, eval y (F k) = 0) → y ∈ zeroSet K := by
    intro y hy hFy k hk
    have hspan : Ideal.span (Set.range F) ≤ RingHom.ker (eval y) := by
      rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact RingHom.mem_ker.mpr (hFy i)
    have h1 := RingHom.mem_ker.mp (hspan (hcut k hk))
    rw [map_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left hy
  refine ⟨O, {w | (w, (0 : Fin (n - e) → ℂ)) ∈ T}, fun w => Φ.symm (w, 0), hO,
    ⟨⟨hpS, hhp⟩, hT0p⟩, hT.preimage (continuous_id.prodMk continuous_const), ?_, ?_, ?_⟩
  · intro w hw
    have hw1 : (w, (0 : Fin (n - e) → ℂ)) ∈ s := by
      have h2 := hw.2.2
      rw [Set.mem_preimage, Φ.right_inv hw.1] at h2
      exact hT0s h2
    have h1 : AnalyticAt ℂ (fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) w :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (f := fun w : Fin e → ℂ => (w, (0 : Fin (n - e) → ℂ))) (hsan _ hw1) h1
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      refine ⟨hw.2, hzs _ hw.2.1.2 fun k => ?_⟩
      have := congrFun (congrArg Prod.snd (Φ.right_inv hw.1)) k
      rwa [hΦ, hΨ] at this
    · intro w hw w' hw' h
      have h2 : Φ (Φ.symm (w, 0)) = Φ (Φ.symm (w', 0)) := by
        simp only at h; rw [h]
      rw [Φ.right_inv hw.1, Φ.right_inv hw'.1] at h2
      exact congrArg Prod.fst h2
    · rintro y ⟨hyO, hyK⟩
      have hy : Φ y = (evalFam r y, 0) := by
        rw [hΦ, hΨ]; congr 1; funext k; exact hyK _ (hFK k)
      refine ⟨evalFam r y, ⟨?_, ?_⟩, ?_⟩
      · rw [← hy]; exact Φ.map_source hyO.1.1
      · show Φ.symm (evalFam r y, 0) ∈ O
        rw [← hy, Φ.left_inv hyO.1.1]; exact hyO
      · show Φ.symm (evalFam r y, 0) = y
        rw [← hy]; exact Φ.left_inv hyO.1.1
  · intro w hw
    have := congrArg Prod.fst (Φ.right_inv hw.1)
    rwa [hΦ, hΨ] at this
end ReciprocityTheory.AnForm.R
