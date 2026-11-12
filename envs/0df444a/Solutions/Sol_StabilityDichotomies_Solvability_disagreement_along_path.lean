-- Prove2me | solution 1 for StabilityDichotomies.Solvability.disagreement_along_path
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:55:15.078428+00:00
-- url     : https://prove2.me/submissions/580805e9-aa99-4442-98b2-2a66c0051e8a

import Mathlib
import Definitions.Def_StabilityDichotomies_Solvability_Incidence

section
set_option autoImplicit false

namespace StabilityDichotomies.Dev.Disagree

open StabilityDichotomies.Solvability
open scoped Classical

variable {Γ : Language} {V : Type}

lemma nodup_of_minUnsat (I : Instance Γ V) (hI : MinimallyUnsatisfiable I) :
    I.constraints.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  by_contra h
  push_neg at h
  have ha : a ∈ I.constraints := Multiset.count_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hI.2 a ha
  apply hI.1
  refine ⟨z, ?_⟩
  intro d hd
  by_cases hda : d = a
  · subst hda
    apply hz
    show d ∈ I.constraints.erase d
    rw [← Multiset.count_pos, Multiset.count_erase_self]; omega
  · exact hz d ((Multiset.mem_erase_of_ne hda).2 hd)

lemma occ_surj (I : Instance Γ V) {d : Constraint Γ V} (hd : d ∈ I.constraints) :
    ∃ e : Occurrence I, occurrenceConstraint I e = d :=
  List.mem_iff_get.mp (Multiset.mem_toList.mpr hd)

lemma occ_inj (I : Instance Γ V) (hI : MinimallyUnsatisfiable I) :
    Function.Injective (occurrenceConstraint I) := by
  have h1 : I.constraints.toList.Nodup := by
    have := nodup_of_minUnsat I hI
    rw [← Multiset.coe_toList I.constraints] at this
    exact Multiset.coe_nodup.mp this
  exact List.nodup_iff_injective_get.mp h1

lemma mem_delete_iff (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (e f : Occurrence I) (d : Constraint Γ V) (hd : d ∈ I.constraints) (hef : e ≠ f)
    (hde : d = occurrenceConstraint I e) :
    d ∈ (I.delete (occurrenceConstraint I f)).constraints := by
  show d ∈ I.constraints.erase _
  apply (Multiset.mem_erase_of_ne _).2 hd
  rw [hde]; exact fun h => hef (occ_inj I hI h)

/-- reachability from `c` along walks whose variable nodes are in disagreement -/
def Reach (I : Instance Γ V) (x y : V → Bool) (c : Occurrence I) (u : IncidenceVertex I) : Prop :=
  ∃ p : (incidenceGraph I).Walk (.inr c) u, ∀ v : V, Sum.inl v ∈ p.support → x v ≠ y v

lemma reach_step (I : Instance Γ V) (x y : V → Bool) (c : Occurrence I)
    (u w : IncidenceVertex I) (hu : Reach I x y c u) (hadj : (incidenceGraph I).Adj u w)
    (hw : ∀ v, w = Sum.inl v → x v ≠ y v) : Reach I x y c w := by
  obtain ⟨p, hp⟩ := hu
  refine ⟨p.concat hadj, ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_concat] at hv
  simp only [List.concat_eq_append, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | hv
  · exact hp v hv
  · exact hw v hv.symm

theorem disagreement (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (c c' : Occurrence I) (hcc' : c ≠ c') (x y : V → Bool)
    (hx : Solution (I.delete (occurrenceConstraint I c)) x)
    (hy : Solution (I.delete (occurrenceConstraint I c')) y) :
    ∃ p : (incidenceGraph I).Walk (.inr c) (.inr c'),
      p.IsPath ∧ ∀ v : V, Sum.inl v ∈ p.support → x v ≠ y v := by
  have key : Reach I x y c (.inr c') := by
    by_contra hnr
    apply hI.1
    refine ⟨fun v => if Reach I x y c (Sum.inl v) then y v else x v, ?_⟩
    intro d hd
    obtain ⟨e, rfl⟩ := occ_surj I hd
    by_cases hre : Reach I x y c (.inr e)
    · have hec' : e ≠ c' := fun h => hnr (h ▸ hre)
      have hsat : (occurrenceConstraint I e).Satisfied y :=
        hy _ (mem_delete_iff I hI e c' _ hd hec' rfl)
      have : (fun i => (if Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
          then y ((occurrenceConstraint I e).scope i)
          else x ((occurrenceConstraint I e).scope i)))
          = fun i => y ((occurrenceConstraint I e).scope i) := by
        funext i
        by_cases hr : Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
        · simp [hr]
        · by_cases hxy : x ((occurrenceConstraint I e).scope i) = y ((occurrenceConstraint I e).scope i)
          · simp [hr, hxy]
          · exfalso; apply hr
            exact reach_step I x y c (.inr e) _ hre ⟨i, rfl⟩
              (fun v hv => by cases hv; exact hxy)
      unfold Constraint.Satisfied
      rw [this]; exact hsat
    · have hec : e ≠ c := fun h => hre (h ▸ ⟨SimpleGraph.Walk.nil, by simp⟩)
      have hsat : (occurrenceConstraint I e).Satisfied x :=
        hx _ (mem_delete_iff I hI e c _ hd hec rfl)
      have : (fun i => (if Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
          then y ((occurrenceConstraint I e).scope i)
          else x ((occurrenceConstraint I e).scope i)))
          = fun i => x ((occurrenceConstraint I e).scope i) := by
        funext i
        by_cases hr : Reach I x y c (Sum.inl ((occurrenceConstraint I e).scope i))
        · exfalso; apply hre
          obtain ⟨p, hp⟩ := hr
          exact reach_step I x y c _ _ ⟨p, hp⟩ ⟨i, rfl⟩ (fun v hv => by cases hv)
        · simp [hr]
      unfold Constraint.Satisfied
      rw [this]; exact hsat
  obtain ⟨p, hp⟩ := key
  refine ⟨p.bypass, SimpleGraph.Walk.bypass_isPath p, ?_⟩
  intro v hv
  exact hp v (SimpleGraph.Walk.support_bypass_subset_support p hv)

end StabilityDichotomies.Dev.Disagree

namespace StabilityDichotomies.Solvability

theorem chk_disagreement_along_path (Γ : Language) (V : Type) [Fintype V]
    (I : Instance Γ V) (hI : MinimallyUnsatisfiable I)
    (c c' : Occurrence I) (hcc' : c ≠ c') (x y : V → Bool)
    (hx : Solution (I.delete (occurrenceConstraint I c)) x)
    (hy : Solution (I.delete (occurrenceConstraint I c')) y) :
    ∃ p : (incidenceGraph I).Walk (.inr c) (.inr c'),
      p.IsPath ∧ ∀ v : V, Sum.inl v ∈ p.support → x v ≠ y v :=
  StabilityDichotomies.Dev.Disagree.disagreement I hI c c' hcc' x y hx hy

end StabilityDichotomies.Solvability
end

theorem solution : type_of% @StabilityDichotomies.Solvability.chk_disagreement_along_path := @StabilityDichotomies.Solvability.chk_disagreement_along_path
