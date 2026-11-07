-- Prove2me | solution 1 for SensitivityGraphLocal.succeeds_eq
-- status  : ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-06T18:59:07.086827+00:00
-- url     : https://prove2.me/submissions/245818fe-be74-49ff-be75-47ba71dd8b7a

import Definitions.Def_SensitivityGraphLocal

set_option autoImplicit false

namespace SensitivityGraphCheck

/-- A hereditary predicate is bounded by checking only the first forbidden size. -/
theorem card_lt_of_forbidden_size {α : Type} [DecidableEq α]
    (P : Finset α → Prop) (r : ℕ)
    (hereditary : ∀ {I J}, J ⊆ I → P I → P J)
    (forbidden : ∀ I, I.card = r → ¬ P I)
    (I : Finset α) (hI : P I) : I.card < r := by
  by_contra h
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  exact forbidden J hJ (hereditary hJI hI)

/-- The first forbidden subset can be chosen to preserve a distinguished vertex. -/
theorem exists_subset_card_eq_containing {α : Type} [DecidableEq α]
    {I : Finset α} {s : α} {r : ℕ} (hs : s ∈ I)
    (hr : 0 < r) (hcard : r ≤ I.card) :
    ∃ J ⊆ I, J.card = r ∧ s ∈ J := by
  have herase : r - 1 ≤ (I.erase s).card := by
    rw [Finset.card_erase_of_mem hs]
    omega
  obtain ⟨J, hJ, hcardJ⟩ := Finset.exists_subset_card_eq herase
  have hsJ : s ∉ J := by
    intro h
    exact (Finset.mem_erase.mp (hJ h)).1 rfl
  refine ⟨insert s J, Finset.insert_subset hs (hJ.trans (Finset.erase_subset s I)), ?_,
    Finset.mem_insert_self s J⟩
  rw [Finset.card_insert_of_notMem hsJ, hcardJ]
  omega

theorem coherent_bound_of_exact_size (D : RawData)
    (hcheck : ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      I.card = D.ordinaryCutoff →
      ¬ (∀ i ∈ I, ∀ j ∈ I, D.adj i j = true → D.label i j = colors j)) :
    ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      (∀ i ∈ I, ∀ j ∈ I, D.adj i j = true → D.label i j = colors j) →
      I.card < D.ordinaryCutoff := by
  intro I colors hI
  apply card_lt_of_forbidden_size
    (fun J => ∀ i ∈ J, ∀ j ∈ J, D.adj i j = true → D.label i j = colors j)
    D.ordinaryCutoff (fun hJI hP i hi j hj => hP i (hJI hi) j (hJI hj))
    (fun J hJ => hcheck J colors hJ) I hI

theorem defect_hereditary (D : RawData) (q : ℕ)
    (colors : Fin D.vertices → Fin 2) {I J : Finset (Fin D.vertices)}
    (hJI : J ⊆ I)
    (hI : ∀ i ∈ I,
      (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q) :
    ∀ i ∈ J,
      (J.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q := by
  intro i hi
  apply (Finset.card_le_card ?_).trans (hI i (hJI hi))
  intro j hj
  rcases Finset.mem_filter.mp hj with ⟨hj, hprop⟩
  exact Finset.mem_filter.mpr ⟨hJI hj, hprop⟩

theorem defect_bound_of_exact_size (D : RawData) (q r : ℕ)
    (hcheck : ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      I.card = r →
      ¬ (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q)) :
    ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q) →
      I.card < r := by
  intro I colors hI
  exact card_lt_of_forbidden_size
    (fun J => ∀ i ∈ J,
      (J.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q)
    r (fun hJI hP => defect_hereditary D q colors hJI hP)
    (fun J hJ => hcheck J colors hJ) I hI

theorem source_bound_of_exact_size (D : RawData) (hr : 0 < D.sourceCutoff)
    (hcheck : ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      I.card = D.sourceCutoff →
      (∃ s ∈ I, ∀ j ∈ I, j ≠ s → D.adj s j = true) →
      ¬ (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ 0)) :
    ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      (∃ s ∈ I, ∀ j ∈ I, j ≠ s → D.adj s j = true) →
      (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ 0) →
      I.card < D.sourceCutoff := by
  intro I colors hs hI
  by_contra hcard
  obtain ⟨s, hsI, hs⟩ := hs
  obtain ⟨J, hJI, hJcard, hsJ⟩ :=
    exists_subset_card_eq_containing hsI hr (Nat.le_of_not_gt hcard)
  exact hcheck J colors hJcard ⟨s, hsJ, fun j hj hjs => hs j (hJI hj) hjs⟩
    (defect_hereditary D 0 colors hJI hI)

/-- Exact-cardinality local obstruction checks imply the full graph validator. -/
theorem valid_of_exact_size_checks (D : RawData)
    (hvertices : 1 < D.vertices)
    (hordinary : 4 ≤ D.ordinaryCutoff)
    (hsource : 4 ≤ D.sourceCutoff)
    (hzero : SensitivityProfileCycle.extendCutoffs D.cutoffs 0 = D.ordinaryCutoff)
    (hloopless : ∀ i, ¬ D.adj i i = true)
    (hcomplement : ∀ i j, i ≠ j → (D.adj i j = true ↔ ¬ D.adj j i = true))
    (hdegree : ∀ i, (Finset.univ.filter (fun j => D.adj i j = true)).card = D.degree)
    (hcoherent : ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      I.card = D.ordinaryCutoff →
      ¬ (∀ i ∈ I, ∀ j ∈ I, D.adj i j = true → D.label i j = colors j))
    (hdefect : ∀ q : Fin D.toleranceCount,
      ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      I.card = D.cutoffs q →
      ¬ (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ q.val))
    (hsourcecheck : ∀ (I : Finset (Fin D.vertices)) (colors : Fin D.vertices → Fin 2),
      I.card = D.sourceCutoff →
      (∃ s ∈ I, ∀ j ∈ I, j ≠ s → D.adj s j = true) →
      ¬ (∀ i ∈ I,
        (I.filter (fun j => D.adj i j = true ∧ D.label i j ≠ colors j)).card ≤ 0)) :
    D.Valid := by
  exact ⟨hvertices, hordinary, hsource, hzero, hloopless, hcomplement, hdegree,
    coherent_bound_of_exact_size D hcoherent,
    fun q => defect_bound_of_exact_size D q.val (D.cutoffs q) (hdefect q),
    source_bound_of_exact_size D (by omega) hsourcecheck⟩

end SensitivityGraphCheck

namespace SensitivityGraphLocal

theorem localValid_iff_valid (D : SensitivityGraphCheck.RawData) :
    LocalValid D ↔ D.Valid := by
  constructor
  · rintro ⟨hv, ho, hs, hz, hl, hc, hd, hcoh, hdef, hsrc⟩
    apply SensitivityGraphCheck.valid_of_exact_size_checks D hv ho hs hz hl hc hd
    · intro I colors hcard
      exact hcoh I (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩) colors
    · intro q I colors hcard
      exact hdef q I (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩) colors
    · intro I colors hcard
      exact hsrc I (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩) colors
  · rintro ⟨hv, ho, hs, hz, hl, hc, hd, hcoh, hdef, hsrc⟩
    refine ⟨hv, ho, hs, hz, hl, hc, hd, ?_, ?_, ?_⟩
    · intro I hmem colors hI
      have hcard := (Finset.mem_powersetCard.mp hmem).2
      have h := hcoh I colors hI
      omega
    · intro q I hmem colors hI
      have hcard := (Finset.mem_powersetCard.mp hmem).2
      have h := hdef q I colors hI
      omega
    · intro I hmem colors hsource hI
      have hcard := (Finset.mem_powersetCard.mp hmem).2
      have h := hsrc I colors hsource hI
      omega

end SensitivityGraphLocal


set_option autoImplicit false

namespace SensitivityGraphLocal
open SensitivityProfileCycle SensitivityProfileSearch SensitivityVariableWord
open SensitivityGraphCheck

theorem rawStep_eq {n : ℕ} (D : RawData) (h : D.Valid)
    (C : Recipe n) (P : Profile n) :
    rawStep D C P = SensitivityVariableWord.step (D.toGraph h) C P := rfl

theorem rawExpand_eq {n : ℕ} (D : RawData) (h : D.Valid)
    (s : List (Profile n)) :
    rawExpand D s = SensitivityVariableFrontier.expand (D.toGraph h) s := rfl

theorem rawFrontier_eq (D : RawData) (h : D.Valid) (n k : ℕ) :
    rawFrontier D n k = SensitivityVariableFrontier.frontier (D.toGraph h) n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rawFrontier, SensitivityVariableFrontier.frontier, ih]
    rfl

theorem rawSucceeds_eq (D : RawData) (h : D.Valid) (n k : ℕ) :
    rawSucceeds D n k = SensitivityVariableFrontier.succeeds (D.toGraph h) n k := by
  unfold rawSucceeds SensitivityVariableFrontier.succeeds
  rw [rawFrontier_eq D h]
  rfl

end SensitivityGraphLocal

theorem solution (D : SensitivityGraphCheck.RawData) (n k : ℕ) :
    SensitivityGraphLocal.succeeds D n k = SensitivityGraphCheck.succeeds D n k := by
  by_cases h : D.Valid
  · have hl := (SensitivityGraphLocal.localValid_iff_valid D).mpr h
    simp only [SensitivityGraphLocal.succeeds, if_pos hl,
      SensitivityGraphCheck.succeeds, dif_pos h]
    exact SensitivityGraphLocal.rawSucceeds_eq D h n k
  · have hl : ¬ SensitivityGraphLocal.LocalValid D :=
      fun hl => h ((SensitivityGraphLocal.localValid_iff_valid D).mp hl)
    simp only [SensitivityGraphLocal.succeeds, if_neg hl,
      SensitivityGraphCheck.succeeds, dif_neg h]

#print axioms solution
