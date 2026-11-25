-- Prove2me | solution 1 for ReciprocityTheory.AnForm.exists_analytic_graph_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:12.69569+00:00
-- url     : https://prove2.me/submissions/0ed2b035-61ef-4d4b-9398-7b0eb41fcd45

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Theorems.Thm_ReciprocityTheory_AnForm_exists_perm_coord_complement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Function
namespace ReciprocityTheory.AnForm
theorem _root_.solution {e c : ℕ} (f : (Fin (e + c) → ℂ) → (Fin c → ℂ))
    (p : Fin (e + c) → ℂ) (hp : f p = 0) (hf : AnalyticAt ℂ f p)
    (hsurj : Function.Surjective (fderiv ℂ f p)) :
    ∃ (σ : Equiv.Perm (Fin (e + c))) (U : Set (Fin (e + c) → ℂ)) (V : Set (Fin e → ℂ))
      (g : (Fin e → ℂ) → (Fin (e + c) → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V {x | x ∈ U ∧ f x = 0} ∧
      ∀ w ∈ V, (fun i => g w (σ (Fin.castAdd c i))) = w := by
  classical
  set A := fderiv ℂ f p with hAdef
  obtain ⟨σ, hσ⟩ := exists_perm_coord_complement (A : (Fin (e + c) → ℂ) →ₗ[ℂ] (Fin c → ℂ)) hsurj
  let Pr : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ (Fin.castAdd c i))
  have hPr : ∀ x, Pr x = fun i => x (σ (Fin.castAdd c i)) := fun x => rfl
  let Lm : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin c → ℂ) := Pr.prod A
  have hinj : Injective Lm := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : Pr v = 0 := congrArg Prod.fst hv
    have h2 : A v = 0 := congrArg Prod.snd hv
    exact hσ v (fun i => by simpa [hPr] using congrFun h1 i) h2
  have hsurjL : Surjective Lm := by
    have hdim : Module.finrank ℂ (Fin (e + c) → ℂ) =
        Module.finrank ℂ ((Fin e → ℂ) × (Fin c → ℂ)) := by
      simp [Module.finrank_prod]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (Lm : (Fin (e + c) → ℂ) →ₗ[ℂ] (Fin e → ℂ) × (Fin c → ℂ)))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective Lm (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurjL)
  have hLe : (Le : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin c → ℂ)) = Lm :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  let φ : (Fin (e + c) → ℂ) → (Fin e → ℂ) × (Fin c → ℂ) := fun x => (Pr x, f x)
  have hφ : HasStrictFDerivAt φ (Le : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin c → ℂ)) p := by
    rw [hLe]; exact Pr.hasStrictFDerivAt.prodMk hf.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph φ
  have hΦ : ∀ x, Φ x = (Pr x, f x) := fun x => rfl
  have hpS : p ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hφan : AnalyticAt ℂ Φ p := (Pr.analyticAt p).prod hf
  have hsymm : AnalyticAt ℂ Φ.symm (Φ p) :=
    Φ.analyticAt_symm' (i := Le) hpS hφan hφ.hasFDerivAt.fderiv
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T0, hT0s, hT0o, hT0p⟩ := mem_nhds_iff.mp hs
  refine ⟨σ, Φ.source ∩ Φ ⁻¹' T0, {w | (w, (0 : Fin c → ℂ)) ∈ Φ.target ∩ T0},
    fun w => Φ.symm (w, 0), ?_, ⟨hpS, hT0p⟩, ?_, ?_, ?_, ?_⟩
  · exact Φ.continuousOn.isOpen_inter_preimage Φ.open_source hT0o
  · exact (Φ.open_target.inter hT0o).preimage (continuous_id.prodMk continuous_const)
  · intro w hw
    have h1 : AnalyticAt ℂ (fun w : Fin e → ℂ => (w, (0 : Fin c → ℂ))) w :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (f := fun w : Fin e → ℂ => (w, (0 : Fin c → ℂ))) (hsan _ (hT0s hw.2)) h1
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hr := Φ.right_inv hw.1
      refine ⟨⟨Φ.map_target hw.1, ?_⟩, ?_⟩
      · show Φ (Φ.symm (w, 0)) ∈ T0
        rw [hr]; exact hw.2
      · have := congrArg Prod.snd hr
        rwa [hΦ] at this
    · intro w hw w' hw' h
      have h2 : Φ (Φ.symm (w, 0)) = Φ (Φ.symm (w', 0)) := by
        simp only at h; rw [h]
      rw [Φ.right_inv hw.1, Φ.right_inv hw'.1] at h2
      exact congrArg Prod.fst h2
    · rintro x ⟨⟨hxS, hxT⟩, hx0⟩
      have hx : Φ x = (Pr x, 0) := by rw [hΦ, hx0]
      refine ⟨Pr x, ⟨?_, ?_⟩, ?_⟩
      · rw [← hx]; exact Φ.map_source hxS
      · rw [← hx]; exact hxT
      · show Φ.symm (Pr x, 0) = x
        rw [← hx]; exact Φ.left_inv hxS
  · intro w hw
    have := congrArg Prod.fst (Φ.right_inv hw.1)
    rw [hΦ] at this
    simpa [hPr] using this
end ReciprocityTheory.AnForm
