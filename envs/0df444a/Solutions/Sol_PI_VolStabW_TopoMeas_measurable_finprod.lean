-- Prove2me | solution 1 for PI.VolStabW.TopoMeas.measurable_finprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:57:56.786628+00:00
-- url     : https://prove2.me/submissions/b5fc6a5f-7c59-4ba4-b8a9-2caeb45dce29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasOrbSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMeas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoMeas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Filter Topology PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW.TopoMeas
theorem _root_.solution {X ι : Type} [MeasurableSpace X] [Countable ι] (f : ι → X → ℂ)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x => ∏ᶠ i, f i x) := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  have hfin : ∀ n : ℕ, {i | e i < n}.Finite := fun n =>
    (Set.finite_lt_nat n).preimage he.injOn
  let s : ℕ → Finset ι := fun n => (hfin n).toFinset
  let A : ℕ → Set X := fun n => ⋂ i, ⋂ (_ : n ≤ e i), f i ⁻¹' {1}
  let h : ℕ → X → ℂ := fun n x => if x ∈ A n then ∏ i ∈ s n, f i x else 1
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hf i (measurableSet_singleton 1)
  have hh : ∀ n, Measurable (h n) := fun n =>
    Measurable.ite (hA n) (Finset.measurable_prod (s n) fun i _ => hf i) measurable_const
  refine measurable_of_tendsto_metrizable hh (tendsto_pi_nhds.2 fun x => ?_)
  have hev : ∀ᶠ n in atTop, h n x = ∏ᶠ i, f i x := by
    by_cases hs : (Function.mulSupport fun i => f i x).Finite
    · obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ hs.toFinset, e i < N :=
        ⟨hs.toFinset.sup e + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup hi)⟩
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hxA : x ∈ A n := by
        simp only [A, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
        intro i hi
        by_contra hne
        have : i ∈ hs.toFinset := by simpa using hne
        have := hN i this
        omega
      simp only [h, hxA, if_true]
      refine (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
      intro i hi
      have := hN i (by simpa using hi)
      simp only [s, Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      omega
    · refine Eventually.of_forall fun n => ?_
      have hxA : x ∉ A n := by
        intro hx
        apply hs
        refine (hfin n).subset fun i hi => ?_
        simp only [A, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hx
        by_contra hlt
        exact hi (hx i (not_lt.1 hlt))
      simp only [h, hxA, if_false]
      exact (finprod_of_infinite_mulSupport hs).symm
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
end PI.VolStabW.TopoMeas
