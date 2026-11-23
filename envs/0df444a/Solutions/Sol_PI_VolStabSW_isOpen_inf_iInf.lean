-- Prove2me | solution 1 for PI.VolStabSW.isOpen_inf_iInf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:51:15.209217+00:00
-- url     : https://prove2.me/submissions/bebacc05-3bd2-44e0-9c3d-dc7dffc185f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Set Filter
open scoped Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace PI.VolStabSW
theorem _root_.solution (Λ₀ : AddSubgroup V) (h₀o : IsOpen (Λ₀ : Set V)) {ι : Type}
    (t : Finset ι) (L : ι → AddSubgroup V) (hLo : ∀ i, IsOpen (L i : Set V)) :
    IsOpen ((Λ₀ ⊓ ⨅ i ∈ t, L i : AddSubgroup V) : Set V) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := (0 : V)) ?_
  have h1 : (Λ₀ : Set V) ∈ 𝓝 (0 : V) := h₀o.mem_nhds Λ₀.zero_mem
  have h2 : (⋂ i ∈ t, (L i : Set V)) ∈ 𝓝 (0 : V) :=
    (Filter.biInter_finset_mem t).2 fun i _ => (hLo i).mem_nhds (L i).zero_mem
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Set.mem_iInter, SetLike.mem_coe] at hx1 hx2
  simp only [SetLike.mem_coe, AddSubgroup.mem_inf, AddSubgroup.mem_iInf]
  exact ⟨hx1, fun i hi => hx2 i hi⟩
end PI.VolStabSW
