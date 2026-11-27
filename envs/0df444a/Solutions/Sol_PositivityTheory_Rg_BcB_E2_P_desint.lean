-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.E2.P.desint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:18:39.7705+00:00
-- url     : https://prove2.me/submissions/f0030869-7810-427a-9009-14664a27324b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Desint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E2 PositivityTheory.Rg.BcB.E2.P
namespace PositivityTheory.Rg.BcB.E2.P
theorem _root_.solution : JointRep → Tonelli → WeakAE → EigAE → LocInt → NonZero → Smooth → Desint := by
  intro hJR hTon hWk hEig hLoc hNZ hSm
  intro X ι κ S _ _ _ ν _ _ F W Φ σ g c₀ P hd hW hΦ hσ hc₀ hP
  let _ : MeasurableSpace (Lp ℂ 2 ν) := borel _
  have : BorelSpace (Lp ℂ 2 ν) := ⟨rfl⟩
  obtain ⟨Ψ, hΨm, hΨ⟩ := hJR S ν
  obtain ⟨f, hrep, hinv⟩ : ∃ f : ι → X.G → S → ℂ, (∀ i, IsRep (F i) (f i)) ∧
      ∀ i, ∀ γ ∈ X.Γ, ∀ x s, f i (γ * x) s = f i x s :=
    ⟨fun i x s => Ψ (F i x) s, fun i =>
      ⟨hΨm.comp (((hd.cont i).measurable.comp measurable_fst).prodMk measurable_snd), fun x => hΨ (F i x)⟩,
      fun i γ hγ x s => by simp only [hd.inv i γ hγ x]⟩
  have : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hT : ∀ᵐ s ∂ν, ∀ i, ∫⁻ x, W x * ‖f i x s‖ₑ ^ 2 ∂X.ν < ⊤ :=
    ae_all_iff.2 fun i => hTon X.G S X.ν ν (F i) (f i) W (hrep i) hW (hd.wt i)
  have hE : ∀ᵐ s ∂ν, ∀ c i, ∀ᵐ x ∂X.μ,
      ∑ j, ∫ y, Φ c i j y * conj (f j (x * y) s) ∂X.μ = σ c s * conj (f i x s) :=
    ae_all_iff.2 fun c => hEig X ι S ν F f (Φ c) (σ c) (hσ c).2.choose hd.cont hrep (hΦ c) (hσ c).1
      (hσ c).2.choose_spec (hd.eig c)
  have hL : ∀ᵐ s ∂ν, ∀ i, LocallyIntegrable (fun x => f i x s) X.μ :=
    ae_all_iff.2 fun i => hLoc X S ν (F i) (f i) (hd.cont i) (hrep i)
  have hO : ∀ᵐ s ∂ν, ∀ n, ∑ i, ∫ x, g n i x * conj (f i x s) ∂X.ν = 0 :=
    ae_all_iff.2 fun n => hWk X.G S ι X.ν ν F f (g n) 0 hrep (fun i => (hd.gint n i).1)
      (fun i => (hd.gint n i).2) MemLp.zero (fun h => by rw [hd.orth n h]; simp)
  have hN : ¬ ∀ᵐ s ∂ν, ∀ i, ∀ᵐ x ∂X.μ, f i x s = 0 := by
    intro h
    apply hd.ne
    funext i
    exact hNZ X S ν (F i) (f i) (hd.cont i) (hrep i) (h.mono fun s hs => hs i)
  obtain ⟨s, hsN, hsP, hs0, hsT, hsE, hsL, hsO⟩ :=
    ((not_eventually.1 hN).and_eventually (hP.and (hc₀.and (hT.and (hE.and (hL.and hO)))))).exists
  have huL : ∀ i, LocallyIntegrable (fun x => conj (f i x s)) X.μ := fun i =>
    (hsL i).mono (Complex.continuous_conj.comp_aestronglyMeasurable (hsL i).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simp)
  obtain ⟨f', hf', heig⟩ := hSm X ι κ (fun i x => conj (f i x s)) Φ (fun c => σ c s) c₀ huL
    (fun i γ hγ x => by simp only [hinv i γ hγ x s]) hΦ hs0 hsE
  have hae : ∀ i, f' i =ᵐ[X.ν] fun x => conj (f i x s) := fun i => by
    unfold Ctx.ν; exact ae_restrict_of_ae (hf' i).2.1
  refine ⟨s, hsP, f', ⟨fun i => (hf' i).1, ?_, fun i => (hf' i).2.2, fun i => ?_, heig, fun n => ?_⟩⟩
  · intro h0
    apply hsN
    intro i
    filter_upwards [(hf' i).2.1] with x hx
    simp only [h0, Pi.zero_apply] at hx
    simpa using hx.symm
  · rw [lintegral_congr_ae (g := fun x => W x * ‖f i x s‖ₑ ^ 2)
      ((hae i).mono fun x hx => by simp only [hx, RCLike.enorm_conj])]
    exact hsT i
  · rw [← hsO n]
    refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
    filter_upwards [hae i] with x hx
    rw [hx]
end PositivityTheory.Rg.BcB.E2.P
