-- Prove2me | solution 1 for ObfImpossibility.PseudoOracle.inequality_8
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-23T23:40:43.555385+00:00
-- url     : https://prove2.me/submissions/23cddf97-cc2c-4658-b1fb-0c3a9cc6cedc

import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

open ObfImpossibility.PseudoOracle

namespace PseudoOracleProof

private lemma runAvoid_congr {K L : ℕ} (t : QTree K L)
    (G G' : Fin K → Fin L) (S : Finset (Fin K))
    (hG : ∀ z, z ∉ S → G' z = G z) :
    t.runAvoid G' S = t.runAvoid G S := by
  induction t with
  | out b => rfl
  | query z k ih =>
    by_cases hz : z ∈ S
    · simp [QTree.runAvoid, hz]
    · simpa only [QTree.runAvoid, if_neg hz, hG z hz] using ih (G z)

private lemma runAvoid_eq_of_hits_false {K L : ℕ} (t : QTree K L)
    (G : Fin K → Fin L) (S : Finset (Fin K)) :
    t.hits G S = false → t.runAvoid G S = t.run G := by
  induction t with
  | out b => intro _; rfl
  | query z k ih =>
    intro h
    have hh : z ∉ S ∧ (k (G z)).hits G S = false := by
      simpa [QTree.hits] using h
    simpa only [QTree.runAvoid, if_neg hh.1, QTree.run] using ih (G z) hh.2

private lemma runAvoid_accept_implies_run {K L : ℕ} (t : QTree K L)
    (G : Fin K → Fin L) (S : Finset (Fin K)) :
    t.runAvoid G S = true → t.run G = true := by
  induction t with
  | out b => exact fun h => h
  | query z k ih =>
    intro h
    by_cases hz : z ∈ S
    · simp [QTree.runAvoid, hz] at h
    · have hh : (k (G z)).runAvoid G S = true := by
        simpa only [QTree.runAvoid, if_neg hz] using h
      exact ih (G z) hh

private lemma avg_congr_on {α : Type} (s : Finset α) (f g : α → Bool)
    (h : ∀ a ∈ s, f a = g a) : avg s f = avg s g := by
  classical
  have hs : s.filter (fun a => f a = true) = s.filter (fun a => g a = true) := by
    apply Finset.filter_congr
    intro a ha
    rw [h a ha]
  unfold avg
  rw [hs]

private lemma avg_mono_on {α : Type} (s : Finset α) (f g : α → Bool)
    (h : ∀ a ∈ s, f a = true → g a = true) : avg s f ≤ avg s g := by
  classical
  have hs : s.filter (fun a => f a = true) ⊆ s.filter (fun a => g a = true) := by
    intro a ha
    obtain ⟨has, haf⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨has, h a has haf⟩
  unfold avg
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card hs
  · positivity

end PseudoOracleProof

theorem solution (K L : ℕ) (δ : ℝ) (D : Fin L → QTree K L) (G : Fin K ↪ Fin L)
    (SG : Finset (Fin K))
    (hprop2 : ∀ x ∈ SG, (D (G x)).hits G SG = false)
    (hgap : 1 / (2 * (K : ℝ) ^ δ) <
      avg SG (fun x => (D (G x)).run G) - avg (LG G SG) (fun y => (D y).run G)) :
    (∀ G' : Fin K ↪ Fin L, (∀ z, z ∉ SG → G' z = G z) →
        ∀ y, (D y).runAvoid G' SG = (D y).runAvoid G SG) ∧
      1 / (2 * (K : ℝ) ^ δ) <
        avg SG (fun x => (D (G x)).runAvoid G SG) -
          avg (LG G SG) (fun y => (D y).runAvoid G SG) := by
  constructor
  · intro G' hG' y
    exact PseudoOracleProof.runAvoid_congr (D y) G G' SG hG'
  · have heq : avg SG (fun x => (D (G x)).runAvoid G SG) =
        avg SG (fun x => (D (G x)).run G) :=
      PseudoOracleProof.avg_congr_on SG _ _ (by
        intro x hx
        exact PseudoOracleProof.runAvoid_eq_of_hits_false (D (G x)) G SG (hprop2 x hx))
    have hle : avg (LG G SG) (fun y => (D y).runAvoid G SG) ≤
        avg (LG G SG) (fun y => (D y).run G) :=
      PseudoOracleProof.avg_mono_on (LG G SG) _ _ (by
        intro y _ hy
        exact PseudoOracleProof.runAvoid_accept_implies_run (D y) G SG hy)
    rw [heq]
    exact lt_of_lt_of_le hgap (sub_le_sub_left hle _)

#print axioms solution
