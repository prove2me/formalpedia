-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_proof_ca1c1cb4046c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:04:49.04279+00:00
-- url     : https://prove2.me/submissions/f86e3bca-6b6d-4596-a2de-3c3967be89a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StCriticalFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSheetOnlyNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsSheetOnlyNull_piece_null_9851f5e85d0d
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_osgood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_scaleBlock_mem_zeroLocus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj IsMultiHomogIdeal mcPts segre fibre IsSheet scaleBlock
  scaleBlock_mem_zeroLocus segre_differentiableAt osgood fibreFinite)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
theorem _root_.solution (hC : CriticalFibreInfinite.Statement) : PtsSheetOnlyNull.Statement := by
  intro K _ ι _ P e Ψ Ψ' hP hΨ hΨ'
  classical
  have hloc : ∀ p : (Fin e → ℂ) × (((k : K) → ι k) → ℂ), ∃ (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ)
      (O : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))), IsOpen O ∧
      (∀ q ∈ O, (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ mcPts P ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
        (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1))) ∧
      (p.2 ∈ fibre P Ψ p.1 → IsSimpleSheetPt P Ψ p.2 → p ∈ O) := by
    intro p
    by_cases hp : p.2 ∈ fibre P Ψ p.1 ∧ IsSimpleSheetPt P Ψ p.2
    · obtain ⟨hpf, y0, γ, ⟨hseg, hsh⟩, hun⟩ := hp
      have hy0 : y0 = p.1 := by
        obtain ⟨z, -, -, hΨz⟩ := hpf
        have h1 := hsh.self_of_nhds.2.2
        rw [hseg, hΨz] at h1
        funext i
        have hi := congrFun h1 i.succ
        simp only [Fin.cons_succ] at hi
        exact hi.symm
      subst hy0
      have hev : ∀ᶠ q in 𝓝 (p.1, p.2),
          (DifferentiableAt ℂ γ q.1 ∧ γ q.1 ∈ mcPts P ∧ Ψ (segre (γ q.1)) = Fin.cons 1 q.1) ∧
            (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)) :=
        ((continuous_fst.tendsto (p.1, p.2)).eventually hsh).and hun
      obtain ⟨O, hO, hOo, hpO⟩ := eventually_nhds_iff.1 hev
      exact ⟨γ, O, hOo, hO, fun _ _ => hpO⟩
    · exact ⟨fun _ _ => 0, ∅, isOpen_empty, by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  choose γ O hOo hO hpO using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun p _ =>
    piece_null hC hP hΨ' (hOo p) (hO p))
  rintro y ⟨w, hwf, hws, hwn⟩
  have hmem : (y, w) ∈ ⋃ p ∈ T, O p := hTU ▸ Set.mem_iUnion.2 ⟨(y, w), hpO (y, w) hwf hws⟩
  obtain ⟨p, hpT, hyw⟩ := Set.mem_iUnion₂.1 hmem
  have hw : w = segre (γ p y) := ((hO p) (y, w) hyw).2 hwf
  subst hw
  exact Set.mem_biUnion hpT ⟨hyw, hwn⟩
end GroundTheory.Heights₂.Heights.PtsSheetOnlyNull
