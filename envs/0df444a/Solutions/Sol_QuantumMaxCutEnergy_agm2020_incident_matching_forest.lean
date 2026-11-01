-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm2020_incident_matching_forest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T01:06:04.547194+00:00
-- url     : https://prove2.me/submissions/4a5bf55c-5a4d-4300-9da3-a536efe2328f

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

open scoped BigOperators


noncomputable section
namespace QuantumMaxCutEnergy.Star

def endpoints {n : ℕ} (e : Edge n) : Finset (Fin n) := {e.val.1, e.val.2}

def IsMatching {n : ℕ} (m : Finset (Edge n)) : Prop :=
  ∀ e ∈ m, ∀ f ∈ m, e ≠ f → Disjoint (endpoints e) (endpoints f)


end QuantumMaxCutEnergy.Star
end

-- Local source: published-agm/IncidentDecomposition.lean

/-!
Published source: Anshu, Gosset, Morenz, TQC 2020,
doi:10.4230/LIPIcs.TQC.2020.7, Lemma 7, pp. 7:9–7:10.
This file isolates the matching and weight-identity part of that lemma.
It does not yet claim that the selected-edge set is a forest, or a runtime bound.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM.Incident
open QuantumMaxCutEnergy.Star

def selectedEdges {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) :
    Finset (Edge n) := E.filter (fun e => ∃ v, I v = some e)

def mutualEdges {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) :
    Finset (Edge n) := E.filter (fun e => I e.val.1 = some e ∧ I e.val.2 = some e)

def selectedWeight {n : ℕ} (w : Weights n) (I : Fin n → Option (Edge n))
    (v : Fin n) : ℝ := (I v).elim 0 (fun e => (w e : ℝ))

def ValidSelector {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) : Prop :=
  ∀ v e, I v = some e → e ∈ E ∧ v ∈ endpoints e

lemma mutual_selected_at {n : ℕ} (E : Finset (Edge n)) (I : Fin n → Option (Edge n))
    (e : Edge n) (he : e ∈ mutualEdges E I) (v : Fin n) (hv : v ∈ endpoints e) :
    I v = some e := by
  have h := (Finset.mem_filter.mp he).2
  simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact h.1
  · exact h.2

theorem mutual_isMatching {n : ℕ} (E : Finset (Edge n))
    (I : Fin n → Option (Edge n)) : IsMatching (mutualEdges E I) := by
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  have h := (mutual_selected_at E I e he v hve).symm.trans
    (mutual_selected_at E I f hf v hvf)
  exact hef (Option.some.inj h)

lemma mutual_subset_selected {n : ℕ} (E : Finset (Edge n))
    (I : Fin n → Option (Edge n)) : mutualEdges E I ⊆ selectedEdges E I := by
  intro e he
  have h := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨h.1, e.val.1, h.2.1⟩

lemma selected_iff_endpoints {n : ℕ} (E : Finset (Edge n))
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) (e : Edge n) :
    (∃ v, I v = some e) ↔ I e.val.1 = some e ∨ I e.val.2 = some e := by
  constructor
  · rintro ⟨v, hv⟩
    have hinc := (hI v e hv).2
    simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hinc
    rcases hinc with rfl | rfl
    · exact Or.inl hv
    · exact Or.inr hv
  · rintro (h | h)
    · exact ⟨e.val.1, h⟩
    · exact ⟨e.val.2, h⟩

lemma selectedWeight_eq_sum {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) (v : Fin n) :
    selectedWeight w I v = ∑ e ∈ E, if I v = some e then (w e : ℝ) else 0 := by
  classical
  cases hv : I v with
  | none => simp [selectedWeight, hv]
  | some e =>
      have he := (hI v e hv).1
      simp [selectedWeight, hv, he]

lemma selected_edge_multiplicity {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) (e : Edge n) :
    (∑ v, if I v = some e then (w e : ℝ) else 0) =
      (if I e.val.1 = some e then (w e : ℝ) else 0) +
      (if I e.val.2 = some e then (w e : ℝ) else 0) := by
  classical
  have hrestrict : (∑ v ∈ endpoints e, if I v = some e then (w e : ℝ) else 0) =
      ∑ v, if I v = some e then (w e : ℝ) else 0 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hnot : I v ≠ some e := by
      intro h
      exact hv (hI v e h).2
    simp [hnot]
  rw [← hrestrict]
  unfold endpoints
  rw [Finset.sum_insert (by simpa using (ne_of_lt e.property)), Finset.sum_singleton]

/-- The exact double-counting identity in the proof of published Lemma 7.
Acyclicity of selectedEdges requires the additional global ordering condition. -/
theorem incident_weight_identity {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (I : Fin n → Option (Edge n)) (hI : ValidSelector E I) :
    (∑ v, selectedWeight w I v) =
      (∑ e ∈ mutualEdges E I, (w e : ℝ)) +
      ∑ e ∈ selectedEdges E I, (w e : ℝ) := by
  classical
  simp_rw [selectedWeight_eq_sum E w I hI]
  rw [Finset.sum_comm]
  simp_rw [selected_edge_multiplicity E w I hI]
  simp only [mutualEdges, selectedEdges, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  simp only [selected_iff_endpoints E I hI e]
  by_cases hl : I e.val.1 = some e <;> by_cases hr : I e.val.2 = some e <;>
    simp [hl, hr, two_mul]

def incidentEdges {n : ℕ} (E : Finset (Edge n)) (v : Fin n) : Finset (Edge n) :=
  E.filter (fun e => v ∈ endpoints e)

def maximumIncident {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (v : Fin n) : Option (Edge n) :=
  if h : (incidentEdges E v).Nonempty then
    some (Classical.choose ((incidentEdges E v).exists_max_image w h))
  else none

theorem maximumIncident_valid {n : ℕ} (E : Finset (Edge n)) (w : Weights n) :
    ValidSelector E (maximumIncident E w) := by
  intro v e he
  unfold maximumIncident at he
  split_ifs at he with h
  · have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image w h)
    have heq := Option.some.inj he
    subst e
    exact Finset.mem_filter.mp hm.1

theorem maximumIncident_max {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (v : Fin n) (e : Edge n) (he : e ∈ E) (hv : v ∈ endpoints e) :
    (w e : ℝ) ≤ selectedWeight w (maximumIncident E w) v := by
  have he' : e ∈ incidentEdges E v := Finset.mem_filter.mpr ⟨he, hv⟩
  have hn : (incidentEdges E v).Nonempty := ⟨e, he'⟩
  have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image w hn)
  simp only [selectedWeight, maximumIncident, dif_pos hn, Option.elim_some]
  exact_mod_cast hm.2 e he'


end QuantumMaxCutEnergy.PublishedAGM.Incident

end

-- Local source: published-agm/IncidentForest.lean

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM.Incident
open QuantumMaxCutEnergy.Star

def edgeGraph {n : ℕ} (F : Finset (Edge n)) : SimpleGraph (Fin n) :=
  ⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2

@[simp] lemma edgeGraph_empty (n : ℕ) : edgeGraph (∅ : Finset (Edge n)) = ⊥ := by
  simp [edgeGraph]

lemma edgeGraph_insert {n : ℕ} (e : Edge n) (F : Finset (Edge n)) :
    edgeGraph (insert e F) = edgeGraph F ⊔ SimpleGraph.edge e.val.1 e.val.2 := by
  ext a b
  simp [edgeGraph, SimpleGraph.iSup_adj, or_comm, or_left_comm, or_assoc]

lemma edgeGraph_adj_endpoint {n : ℕ} (F : Finset (Edge n)) (v u : Fin n)
    (h : (edgeGraph F).Adj v u) : ∃ e ∈ F, v ∈ endpoints e := by
  simp only [edgeGraph, SimpleGraph.iSup_adj, exists_prop] at h
  obtain ⟨e, he, hadj⟩ := h
  refine ⟨e, he, ?_⟩
  rcases (SimpleGraph.edge_adj e.val.1 e.val.2 v u).mp hadj with ⟨h | h, _⟩
  · simp [endpoints, h.1]
  · simp [endpoints, h.1]

lemma edgeGraph_isolated {n : ℕ} (F : Finset (Edge n)) (v : Fin n)
    (hv : ∀ e ∈ F, v ∉ endpoints e) : (edgeGraph F).neighborSet v = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  intro u hu
  obtain ⟨e, he, hve⟩ := edgeGraph_adj_endpoint F v u hu
  exact hv e he hve

/-- Global tie breaking is essential: local maximum choices can create cycles
when several incident weights tie. Injective priorities prevent that issue. -/
theorem selectedEdges_isAcyclic {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (I : Fin n → Option (Edge n)) (hI : ValidSelector E I)
    (priority : Edge n → β) (hinj : Function.Injective priority)
    (hmax : ∀ v e, I v = some e → ∀ f ∈ E, v ∈ endpoints f → priority f ≤ priority e) :
    (edgeGraph (selectedEdges E I)).IsAcyclic := by
  classical
  suffices h : ∀ F : Finset (Edge n), F ⊆ selectedEdges E I → (edgeGraph F).IsAcyclic by
    exact h _ (Finset.Subset.refl _)
  intro F
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    intro hF
    by_cases hne : F.Nonempty
    · obtain ⟨e, he, hmin⟩ := F.exists_min_image priority hne
      obtain ⟨v, hv⟩ := (Finset.mem_filter.mp (hF he)).2
      have hve := (hI v e hv).2
      have hfresh : ∀ f ∈ F.erase e, v ∉ endpoints f := by
        intro f hf hvf
        have hfm := (Finset.mem_erase.mp hf).2
        have hfe := (Finset.mem_filter.mp (hF hfm)).1
        have hle := hmax v e hv f hfe hvf
        have hge := hmin f hfm
        exact (Finset.mem_erase.mp hf).1 (hinj (le_antisymm hle hge))
      have hacyc := ih (F.erase e) (Finset.erase_ssubset he)
        (fun f hf => hF (Finset.mem_erase.mp hf).2)
      have hnr : ¬(edgeGraph (F.erase e)).Reachable e.val.1 e.val.2 := by
        have hi := edgeGraph_isolated (F.erase e) v hfresh
        simp only [endpoints, Finset.mem_insert, Finset.mem_singleton] at hve
        rcases hve with rfl | rfl
        · exact SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
            (ne_of_lt e.property) hi
        · exact SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
            (ne_of_lt e.property) hi
      have heq : F = insert e (F.erase e) := (Finset.insert_erase he).symm
      rw [heq, edgeGraph_insert]
      exact hacyc.sup_edge_of_not_reachable hnr
    · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hz]

def rankIncident {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (priority : Edge n → β) (v : Fin n) : Option (Edge n) :=
  if h : (incidentEdges E v).Nonempty then
    some (Classical.choose ((incidentEdges E v).exists_max_image priority h))
  else none

lemma rankIncident_valid {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (priority : Edge n → β) :
    ValidSelector E (rankIncident E priority) := by
  intro v e he
  unfold rankIncident at he
  split_ifs at he with h
  have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image priority h)
  have heq := Option.some.inj he
  subst e
  exact Finset.mem_filter.mp hm.1

lemma rankIncident_max {n : ℕ} {β : Type*} [LinearOrder β]
    (E : Finset (Edge n)) (priority : Edge n → β) (v : Fin n) (e : Edge n)
    (he : rankIncident E priority v = some e) (f : Edge n)
    (hf : f ∈ E) (hv : v ∈ endpoints f) : priority f ≤ priority e := by
  have hf' : f ∈ incidentEdges E v := Finset.mem_filter.mpr ⟨hf, hv⟩
  have hn : (incidentEdges E v).Nonempty := ⟨f, hf'⟩
  have hm := Classical.choose_spec ((incidentEdges E v).exists_max_image priority hn)
  simp only [rankIncident, dif_pos hn, Option.some.injEq] at he
  rw [← he]
  exact hm.2 f hf'

def weightPriority {n : ℕ} (w : Weights n) (e : Edge n) : ℚ≥0 ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (w e, toLex (e.val.1.val, e.val.2.val))

lemma weightPriority_injective {n : ℕ} (w : Weights n) :
    Function.Injective (weightPriority w) := by
  intro e f h
  have hpair : (e.val.1.val, e.val.2.val) = (f.val.1.val, f.val.2.val) :=
    congrArg (fun x : ℚ≥0 ×ₗ (ℕ ×ₗ ℕ) => ofLex (ofLex x).2) h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst hpair)
  · exact Fin.ext (congrArg Prod.snd hpair)

lemma weight_le_of_priority {n : ℕ} (w : Weights n) (e f : Edge n)
    (h : weightPriority w e ≤ weightPriority w f) : w e ≤ w f := by
  rcases Prod.Lex.toLex_le_toLex.mp h with hl | ⟨he, _⟩
  · exact hl.le
  · exact he.le


end QuantumMaxCutEnergy.PublishedAGM.Incident

end

-- Local source: published-agm/IncidentLemma7.lean

/-!
The complete finite combinatorial content of published TQC2020 Lemma 7,
pp. 7:9–7:10. The theorem includes actual Mathlib graph acyclicity.
It does not assert the paper's efficient-computation claim.
-/

noncomputable section
open scoped BigOperators

namespace QuantumMaxCutEnergy.PublishedAGM.Incident
open QuantumMaxCutEnergy.Star

def incidentMaximum {n : ℕ} (E : Finset (Edge n)) (w : Weights n) (v : Fin n) : ℚ≥0 :=
  (incidentEdges E v).sup w

lemma rankIncident_weight_eq_max {n : ℕ} (E : Finset (Edge n)) (w : Weights n)
    (v : Fin n) :
    selectedWeight w (rankIncident E (weightPriority w)) v = (incidentMaximum E w v : ℝ) := by
  classical
  by_cases h : (incidentEdges E v).Nonempty
  · have hm := Classical.choose_spec
      ((incidentEdges E v).exists_max_image (weightPriority w) h)
    let e := Classical.choose ((incidentEdges E v).exists_max_image (weightPriority w) h)
    have hemax : ∀ f ∈ incidentEdges E v, w f ≤ w e := by
      intro f hf
      exact weight_le_of_priority w f e (hm.2 f hf)
    have heq : incidentMaximum E w v = w e :=
      le_antisymm (Finset.sup_le hemax) (Finset.le_sup hm.1)
    simp only [selectedWeight, rankIncident, dif_pos h, Option.elim_some, heq]
    rfl
  · have he : incidentEdges E v = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [selectedWeight, rankIncident, h, incidentMaximum, he]

theorem exists_incident_matching_forest {n : ℕ} (E : Finset (Edge n)) (w : Weights n) :
    ∃ M F : Finset (Edge n), M ⊆ E ∧ F ⊆ E ∧ M ⊆ F ∧ IsMatching M ∧
      (edgeGraph F).IsAcyclic ∧
      (∑ v, (incidentMaximum E w v : ℝ)) =
        (∑ e ∈ M, (w e : ℝ)) + ∑ e ∈ F, (w e : ℝ) := by
  classical
  let I := rankIncident E (weightPriority w)
  have hI : ValidSelector E I := rankIncident_valid E (weightPriority w)
  refine ⟨mutualEdges E I, selectedEdges E I, Finset.filter_subset _ _,
    Finset.filter_subset _ _, mutual_subset_selected E I, mutual_isMatching E I, ?_, ?_⟩
  · exact selectedEdges_isAcyclic E I hI (weightPriority w) (weightPriority_injective w)
      (rankIncident_max E (weightPriority w))
  · have hid := incident_weight_identity E w I hI
    simpa only [I, rankIncident_weight_eq_max] using hid

/-- A formulation using only the campaign's input types and Mathlib graph
acyclicity, suitable as a public theorem without additional definitions. -/
theorem published_lemma7_combinatorial {n : ℕ} (E : Finset (Edge n)) (w : Weights n) :
    ∃ M F : Finset (Edge n), M ⊆ E ∧ F ⊆ E ∧ M ⊆ F ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint
        ({e.val.1, e.val.2} : Finset (Fin n)) {f.val.1, f.val.2}) ∧
      (⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2).IsAcyclic ∧
      (∑ v, (((E.filter (fun e => v = e.val.1 ∨ v = e.val.2)).sup w : ℚ≥0) : ℝ)) =
        (∑ e ∈ M, (w e : ℝ)) + ∑ e ∈ F, (w e : ℝ) := by
  simpa only [IsMatching, endpoints, edgeGraph, incidentMaximum, incidentEdges,
    Finset.mem_insert, Finset.mem_singleton] using exists_incident_matching_forest E w


end QuantumMaxCutEnergy.PublishedAGM.Incident

end

theorem solution {n : ℕ} (E : Finset (QuantumMaxCutEnergy.Edge n)) (w : QuantumMaxCutEnergy.Weights n) :
    ∃ M F : Finset (QuantumMaxCutEnergy.Edge n), M ⊆ E ∧ F ⊆ E ∧ M ⊆ F ∧
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint
        ({e.val.1, e.val.2} : Finset (Fin n)) {f.val.1, f.val.2}) ∧
      (⨆ e ∈ F, SimpleGraph.edge e.val.1 e.val.2).IsAcyclic ∧
      (∑ v, (((E.filter (fun e => v = e.val.1 ∨ v = e.val.2)).sup w : ℚ≥0) : ℝ)) =
        (∑ e ∈ M, (w e : ℝ)) + ∑ e ∈ F, (w e : ℝ) := by
  exact QuantumMaxCutEnergy.PublishedAGM.Incident.published_lemma7_combinatorial E w

#print axioms solution
