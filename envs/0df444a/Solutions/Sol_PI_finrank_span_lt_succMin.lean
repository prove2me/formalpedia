-- Prove2me | solution 1 for PI.finrank_span_lt_succMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:28.491899+00:00
-- url     : https://prove2.me/submissions/e37604f0-d65d-42e9-9fb1-85d6fae581d4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_TransferenceKey
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_Minima

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open scoped InnerProductSpace
open PI
variable {N : ℕ}
namespace PI
theorem _root_.solution (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) (hi : 1 ≤ i) :
    finrank ℝ (Submodule.span ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}) < i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ
    {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}
  have hbfin : b.Finite := hbli.setFinite
  letI := hbfin.fintype
  have hcard := finrank_span_set_eq_card hbli
  rw [hbspan] at hcard
  have hle : i ≤ Fintype.card b := by rw [← Set.toFinset_card]; omega
  let e : Fin i ↪ b := (Fin.castLEEmb hle).trans (Fintype.equivFin b).symm.toEmbedding
  let v : Fin i → EuclideanSpace ℝ (Fin N) := fun j => (e j : EuclideanSpace ℝ (Fin N))
  have hvli : LinearIndependent ℝ v := hbli.comp e e.injective
  have hvS : ∀ j, v j ∈ M ∧ ‖v j‖ < succMin M i := fun j => hbS (e j).2
  have hne : (Finset.univ : Finset (Fin i)).Nonempty := ⟨⟨0, hi⟩, Finset.mem_univ _⟩
  have ht_lt : Finset.univ.sup' hne (fun j => ‖v j‖) < succMin M i :=
    (Finset.sup'_lt_iff hne).2 fun j _ => (hvS j).2
  have ht_mem : Finset.univ.sup' hne (fun j => ‖v j‖) ∈ {t : ℝ | 0 ≤ t ∧
      ∃ v : Fin i → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t} :=
    ⟨(norm_nonneg _).trans (Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ ⟨0, hi⟩)),
      v, fun j => (hvS j).1, hvli, fun j => Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ j)⟩
  have hinf := csInf_le ⟨0, fun t ht => ht.1⟩ ht_mem
  exact lt_irrefl (succMin M i) (lt_of_le_of_lt hinf ht_lt)
end PI
