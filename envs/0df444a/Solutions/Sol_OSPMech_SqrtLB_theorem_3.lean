-- Prove2me | solution 1 for OSPMech.SqrtLB.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:53:25.139367+00:00
-- url     : https://prove2.me/submissions/982a2ad6-4dc3-4c83-acb1-bb5481218811

import Mathlib
import Definitions.Def_OSPMech_SqrtLB_Model

namespace OSPMech.SqrtLB

variable {n : ℕ} {X : Type}

/-- A simple walk of length `m` in the OSP graph of agent `i`. -/
def E3Walk (D : Fin n → Finset ℝ) (t : ImplTree n X) (i : Fin n) (m : ℕ)
    (w : ℕ → (Fin n → ℝ)) : Prop :=
  (∀ l ≤ m, InDomain D (w l)) ∧ (∀ l < m, OSPEdge D t i (w l) (w (l + 1))) ∧
    (∀ l ≤ m, ∀ l' ≤ m, w l = w l' → l = l')

/-- Weights of simple walks ending at `b`. -/
def E3Set (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X) (i : Fin n)
    (b : Fin n → ℝ) : Set ℝ :=
  {s | ∃ m w, E3Walk D t i m w ∧ w m = b ∧
    s = ∑ l ∈ Finset.range m, edgeWeight cost t i (w l) (w (l + 1))}

theorem e3_nonempty (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X)
    (i : Fin n) (b : Fin n → ℝ) (hb : InDomain D b) : (E3Set D cost t i b).Nonempty := by
  refine ⟨0, 0, fun _ => b, ⟨fun _ _ => hb, fun l hl => absurd hl (by omega), ?_⟩, rfl, by simp⟩
  intro l hl l' hl' _
  omega

theorem e3_bdd (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X)
    (i : Fin n) (b : Fin n → ℝ) : BddBelow (E3Set D cost t i b) := by
  classical
  have hfin : {b : Fin n → ℝ | InDomain D b}.Finite := by
    have := Set.Finite.pi (t := fun i => (D i : Set ℝ)) (fun i => (D i).finite_toSet)
    convert this using 1
    ext b
    simp [InDomain]
  set V := hfin.toFinset with hV
  have hmemV : ∀ b, InDomain D b → b ∈ V := by
    intro b hb; simp [hV, hb]
  set K : ℝ := ∑ a ∈ V, ∑ b ∈ V, |edgeWeight cost t i a b| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hKle : ∀ a ∈ V, ∀ b ∈ V, |edgeWeight cost t i a b| ≤ K := by
    intro a ha b hb
    calc |edgeWeight cost t i a b| ≤ ∑ b ∈ V, |edgeWeight cost t i a b| :=
          Finset.single_le_sum (f := fun b => |edgeWeight cost t i a b|)
            (fun _ _ => abs_nonneg _) hb
      _ ≤ K := Finset.single_le_sum (f := fun a => ∑ b ∈ V, |edgeWeight cost t i a b|)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) ha
  refine ⟨-(V.card * K), ?_⟩
  rintro s ⟨m, w, ⟨hD, hE, hinj⟩, _, rfl⟩
  have hm : m + 1 ≤ V.card := by
    have := Finset.card_le_card_of_injOn (s := Finset.range (m + 1)) (t := V) w
      (fun l hl => hmemV _ (hD l (by simp at hl; omega)))
      (fun l hl l' hl' h => hinj l (by simp at hl; omega) l' (by simp at hl'; omega) h)
    simpa using this
  have h1 : ∑ l ∈ Finset.range m, |edgeWeight cost t i (w l) (w (l + 1))| ≤ m * K := by
    calc _ ≤ ∑ l ∈ Finset.range m, K := Finset.sum_le_sum (fun l hl => by
          simp at hl
          exact hKle _ (hmemV _ (hD l (by omega))) _ (hmemV _ (hD (l + 1) (by omega))))
      _ = m * K := by simp
  have h2 : -(∑ l ∈ Finset.range m, |edgeWeight cost t i (w l) (w (l + 1))|) ≤
      ∑ l ∈ Finset.range m, edgeWeight cost t i (w l) (w (l + 1)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun l _ => neg_abs_le _)
  have h3 : (m : ℝ) * K ≤ V.card * K := by
    apply mul_le_mul_of_nonneg_right _ hK0
    exact_mod_cast (by omega : m ≤ V.card)
  linarith


theorem e3_step (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ) (t : ImplTree n X)
    (i : Fin n) (hno : NoNegCycle D cost t i) (b b' : Fin n → ℝ) (hE : OSPEdge D t i b b')
    (s : ℝ) (hs : s ∈ E3Set D cost t i b) :
    ∃ s' ∈ E3Set D cost t i b', s' ≤ s + edgeWeight cost t i b b' := by
  classical
  obtain ⟨m, w, ⟨hD, hEw, hinj⟩, hwm, rfl⟩ := hs
  by_cases hmem : ∃ q ≤ m, w q = b'
  · obtain ⟨q, hq, hwq⟩ := hmem
    refine ⟨∑ l ∈ Finset.range q, edgeWeight cost t i (w l) (w (l + 1)), ⟨q, w,
      ⟨fun l hl => hD l (by omega), fun l hl => hEw l (by omega),
        fun l hl l' hl' h => hinj l (by omega) l' (by omega) h⟩, hwq, rfl⟩, ?_⟩
    -- the cycle
    obtain ⟨k, hk⟩ : ∃ k, m = q + k := ⟨m - q, by omega⟩
    have hcyc := hno k (fun j => w (q + j)) (by
      intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.val_last]
        rw [finRotate_last]
        simp only [Fin.val_zero, add_zero]
        rw [show q + k = m by omega, hwq, hwm]
        exact hE
      | cast j' =>
        rw [finRotate_succ_apply, Fin.coeSucc_eq_succ]
        simp only [Fin.coe_castSucc, Fin.val_succ]
        rw [← add_assoc]
        exact hEw _ (by have := j'.isLt; omega))
    rw [Fin.sum_univ_castSucc] at hcyc
    simp only [Fin.coe_castSucc, Fin.val_last] at hcyc
    have h1 : ∀ j' : Fin k, edgeWeight cost t i (w (q + j')) (w (q + ((finRotate (k + 1))
        (Fin.castSucc j') : ℕ))) = edgeWeight cost t i (w (q + j')) (w (q + j' + 1)) := by
      intro j'
      rw [finRotate_succ_apply, Fin.coeSucc_eq_succ, Fin.val_succ, ← add_assoc]
    simp only [h1] at hcyc
    rw [Fin.sum_univ_eq_sum_range (fun l => edgeWeight cost t i (w (q + l)) (w (q + l + 1))) k]
      at hcyc
    rw [finRotate_last] at hcyc
    simp only [Fin.val_zero, add_zero] at hcyc
    rw [show q + k = m by omega, hwq, hwm] at hcyc
    have h2 : ∑ l ∈ Finset.range m, edgeWeight cost t i (w l) (w (l + 1)) =
        ∑ l ∈ Finset.range q, edgeWeight cost t i (w l) (w (l + 1)) +
        ∑ l ∈ Finset.range k, edgeWeight cost t i (w (q + l)) (w (q + l + 1)) := by
      rw [hk, Finset.sum_range_add]
    rw [h2]
    linarith
  · push Not at hmem
    set w' : ℕ → (Fin n → ℝ) := fun l => if l ≤ m then w l else b' with hw'
    have hw'le : ∀ l ≤ m, w' l = w l := fun l hl => by simp [hw', hl]
    have hw'gt : w' (m + 1) = b' := by simp [hw']
    refine ⟨∑ l ∈ Finset.range (m + 1), edgeWeight cost t i (w' l) (w' (l + 1)),
      ⟨m + 1, w', ⟨?_, ?_, ?_⟩, hw'gt, rfl⟩, ?_⟩
    · intro l hl
      by_cases h : l ≤ m
      · rw [hw'le l h]; exact hD l h
      · simp only [hw', h, if_false]; exact hE.2.1
    · intro l hl
      by_cases h : l < m
      · rw [hw'le l (by omega), hw'le (l + 1) (by omega)]; exact hEw l h
      · have : l = m := by omega
        subst this
        rw [hw'le l le_rfl, hw'gt, hwm]; exact hE
    · intro l hl l' hl' h
      by_cases h1 : l ≤ m <;> by_cases h2 : l' ≤ m
      · rw [hw'le l h1, hw'le l' h2] at h; exact hinj l h1 l' h2 h
      · have : l' = m + 1 := by omega
        subst this
        rw [hw'le l h1, hw'gt] at h
        exact absurd h (hmem l h1)
      · have : l = m + 1 := by omega
        subst this
        rw [hw'le l' h2, hw'gt] at h
        exact absurd h.symm (hmem l' h2)
      · omega
    · rw [Finset.sum_range_succ]
      apply le_of_eq
      congr 1
      · apply Finset.sum_congr rfl
        intro l hl
        simp only [Finset.mem_range] at hl
        rw [hw'le l (by omega), hw'le (l + 1) (by omega)]
      · rw [hw'le m le_rfl, hw'gt, hwm]

end OSPMech.SqrtLB

open OSPMech.SqrtLB

theorem solution {n : ℕ} {X : Type} (D : Fin n → Finset ℝ) (cost : Fin n → ℝ → X → ℝ)
    (t : ImplTree n X) :
    (∃ p : (Fin n → ℝ) → Fin n → ℝ, IsOSP D cost t p) ↔ ∀ i, NoNegCycle D cost t i := by
  classical
  constructor
  · rintro ⟨p, hp⟩ i k w hedge
    have key : ∀ j, p (w (finRotate (k + 1) j)) i - p (w j) i ≤
        edgeWeight cost t i (w j) (w (finRotate (k + 1) j)) := by
      intro j
      obtain ⟨hD1, hD2, pos, hd⟩ := hedge j
      have := hp pos i (w j) (w (finRotate (k + 1) j)) hD1 hD2 hd
      simp only [edgeWeight]
      linarith
    have hsum : ∑ j, (p (w (finRotate (k + 1) j)) i - p (w j) i) = 0 := by
      rw [Finset.sum_sub_distrib,
        Equiv.sum_comp (finRotate (k + 1)) (fun j => p (w j) i)]
      simp
    calc (0 : ℝ) = ∑ j, (p (w (finRotate (k + 1) j)) i - p (w j) i) := hsum.symm
      _ ≤ _ := Finset.sum_le_sum (fun j _ => key j)
  · intro h
    have hφ : ∀ i, ∃ φ : (Fin n → ℝ) → ℝ, ∀ b b', OSPEdge D t i b b' →
        φ b' - φ b ≤ edgeWeight cost t i b b' := by
      intro i
      refine ⟨fun b => sInf (E3Set D cost t i b), ?_⟩
      intro b b' hE
      have hne := e3_nonempty D cost t i b hE.1
      have : sInf (E3Set D cost t i b') - edgeWeight cost t i b b' ≤ sInf (E3Set D cost t i b) :=
        le_csInf hne (fun s hs => by
          obtain ⟨s', hs', hle⟩ := e3_step D cost t i (h i) b b' hE s hs
          have := csInf_le (e3_bdd D cost t i b') hs'
          linarith)
      linarith
    choose φ hφ using hφ
    refine ⟨fun b i => φ i b, ?_⟩
    intro pos i b bDev hb hbd hd
    have hE : OSPEdge D t i b bDev := ⟨hb, hbd, pos, hd⟩
    have := hφ i b bDev hE
    simp only [edgeWeight] at this
    linarith
