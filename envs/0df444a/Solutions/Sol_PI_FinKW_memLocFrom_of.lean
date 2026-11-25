-- Prove2me | solution 1 for PI.FinKW.memLocFrom_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:52:49.497141+00:00
-- url     : https://prove2.me/submissions/bf55a862-61c4-4e06-9f45-f2d2548f00a1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_MemLocFrom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_LocFrom
import Theorems.Thm_P2M_PI_FinKW_ratV_add__0cc5b55a46e7
import Theorems.Thm_P2M_PI_FinKW_ratV_zero__d853635dcea6
import Theorems.Thm_P2M_PI_FinKW_ratV_zsmul__e750ac2a41e7
import Theorems.Thm_PI_FinKW_psiV_entry
import Theorems.Thm_P2M_PI_FinKW_smul_one_tmul__5e47ee373b19
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.FinKW
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
namespace PI.FinKW
theorem _root_.solution (hI : InjV) : MemLocFrom := by
  intro I x hx
  obtain ⟨s, hs⟩ := Submodule.FG.restrictScalars (R := ℤ) I.L_fg
  let g : s → (Fin I.n → I.E) := fun j => (j : Fin I.n → I.E)
  have hgL : ∀ j, g j ∈ I.L := fun j => by
    have : (j : Fin I.n → I.E) ∈ I.L.restrictScalars ℤ := hs ▸ Submodule.subset_span j.2
    exact this
  have hloc : ∀ v : HeightOneSpectrum (𝓞 I.F), ∃ c : s → v.adicCompletionIntegers I.F,
      ∑ j, c j • Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (g j) = vecV I v x := by
    intro v
    rw [← Submodule.mem_span_range_iff_exists_fun]
    have hle : Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) ≤
        Submodule.span (v.adicCompletionIntegers I.F)
          (Set.range fun j => Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (g j)) := by
      rw [Formalism.L2.SG.Sub.latLoc, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      have hl' : l ∈ Submodule.span ℤ (s : Set (Fin I.n → I.E)) := by rw [hs]; exact hl
      clear hl
      induction hl' using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
      | zero => rw [ratV_zero']; exact zero_mem _
      | add a b _ _ ha hb => rw [ratV_add']; exact add_mem ha hb
      | smul k a _ ha => rw [ratV_zsmul']; exact zsmul_mem ha k
    exact hle (hx v)
  choose c hc using hloc
  let α : s → Formalism.MainNotions.S.Af I.F := fun j =>
    RestrictedProduct.mk (fun v => ((c v j : v.adicCompletionIntegers I.F) : v.adicCompletion I.F))
      (Filter.Eventually.of_forall fun v => (c v j).2)
  have hαint : ∀ j, α j ∈ Formalism.UG.intAd I.F := fun j v => (c v j).2
  have hαmem : ∀ j, (1 : I.E) ⊗ₜ[I.F] α j ∈ Formalism.MainNotions.S.IntAf I.F I.E := fun j =>
    Subring.subset_closure (Or.inr ⟨⟨α j, hαint j⟩, rfl⟩)
  let y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F :=
    ∑ j, (⟨_, hαmem j⟩ : Formalism.MainNotions.S.IntAf I.F I.E) •
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (g j i))
  have hy : y ∈ I.Lf := Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨g j, hgL j⟩, rfl⟩)
  have hyx : y = x := by
    funext i
    rw [← sub_eq_zero]
    apply hI I
    intro v
    rw [map_sub, sub_eq_zero]
    have hci := congrFun (hc v) i
    simp only [vecV] at hci
    rw [← hci]
    simp only [y, Finset.sum_apply, map_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subring.smul_def, smul_eq_mul]
    change psiV I v (((1 : I.E) ⊗ₜ[I.F] α j) * (g j i ⊗ₜ[I.F] (1 : Formalism.MainNotions.S.Af I.F))) = _
    rw [psiV_entry]
    change _ = c v j • ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) ⊗ₜ[I.F] g j i)
    rw [smul_one_tmul']
    rfl
  exact hyx ▸ hy
end PI.FinKW
