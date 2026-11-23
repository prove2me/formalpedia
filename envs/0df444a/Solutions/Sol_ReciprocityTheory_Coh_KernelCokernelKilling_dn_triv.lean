-- Prove2me | solution 1 for ReciprocityTheory.Coh.KernelCokernelKilling.dn_triv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:51.808837+00:00
-- url     : https://prove2.me/submissions/0a3e94dd-f36e-435c-8426-d9cfc20da815

import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_ConnNatHolds
import Definitions.Def_ReciprocityTheory_GroupCohomology_PairHomFCoeOfId
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
import Definitions.Def_ReciprocityTheory_GroupCohomology_ShiftA
import Theorems.Thm_ReciprocityTheory_Gal_dn_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.KernelCokernelKilling
variable {R : Type u} [CommRing R] {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Subsingleton H]
namespace ReciprocityTheory.Coh.KernelCokernelKilling
theorem _root_.solution {V : Type u} [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul R V] (rho : Representation R H V) (n : ℕ) (f : (Fin n → H) → V)
    (g : Fin (n + 1) → H) (a : Fin n → H) :
    dn rho n f g = (1 + ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1)) • f a := by
  rw [dn_apply, Subsingleton.elim (g 0) 1, map_one, Module.End.one_apply,
    Subsingleton.elim (fun i => g i.succ) a, add_smul, one_smul, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Subsingleton.elim (Fin.contractNth j (· * ·) g) a]
end ReciprocityTheory.Coh.KernelCokernelKilling
