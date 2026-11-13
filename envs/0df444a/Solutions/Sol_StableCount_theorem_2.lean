-- Prove2me | solution 1 for StableCount.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:10:44.647195+00:00
-- url     : https://prove2.me/submissions/30df5aba-4c37-4f2a-a736-c25a5fc68b72

import Mathlib
import Theorems.Thm_StableCount_lemma_2_4
import Theorems.Thm_StableCount_lemma_3_7
import Theorems.Thm_StableCount_proposition_4_2

section
namespace StableCount

open StableMatching

namespace Dev.T2

variable {n : ℕ}

theorem W_nonneg (h : ℕ → ℝ) (hh : IsAdmissible h) (d : ℕ) : 0 ≤ W h d :=
  Finset.sum_nonneg fun r hr => (hh.1 r (Finset.mem_Icc.mp hr).1).le

theorem W_lt (h : ℕ → ℝ) (hh : IsAdmissible h) {a b : ℕ} (hab : a < b) : W h a < W h b := by
  unfold W
  refine Finset.sum_lt_sum_of_subset (i := b) ?_ ?_ ?_ (hh.1 b (by omega)) ?_
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · simp only [Finset.mem_Icc]; omega
  · simp only [Finset.mem_Icc]; omega
  · intro j hj _; exact (hh.1 j (Finset.mem_Icc.mp hj).1).le

theorem W_mono (h : ℕ → ℝ) (hh : IsAdmissible h) {a b : ℕ} (hab : a ≤ b) : W h a ≤ W h b := by
  rcases hab.lt_or_eq with h1 | h1
  · exact (W_lt h hh h1).le
  · rw [h1]

theorem sum_dL (Q : Member n) (f : ℕ → ℝ) (s : Sex) :
    ∑ v : Fin n, f (Q.dL s v) = ∑ p : Fin n, f (Q.deg s p) := by
  cases s
  · rfl
  · exact Equiv.sum_comp (Q.μ 0) (fun p => f (Q.deg .woman p))

theorem sum_Fon (Q : Member n) (h : ℕ → ℝ) (s : Sex) (P : Finset (Fin Q.R)) :
    Q.Fon h s P = ∑ p : Fin n, W h (Q.degOn P s p) := by
  unfold Member.Fon
  cases s
  · rfl
  · exact Equiv.sum_comp (Q.μ 0) (fun p => W h (Q.degOn P .woman p))

theorem Fh_eq (Q : Member n) (h : ℕ → ℝ) :
    Q.Fh h = (Q.Fon h .man Finset.univ + Q.Fon h .woman Finset.univ) / 2 := by
  unfold Member.Fh
  rw [Finset.sum_add_distrib, sum_dL Q (W h) .man, sum_dL Q (W h) .woman, sum_Fon, sum_Fon]
  have : ∀ s p, Q.degOn Finset.univ s p = Q.deg s p := by
    intro s p; simp [Member.degOn, Member.deg]
  simp only [this]
  ring

theorem Fh_of_deg (Q Q' : Member n) (h : ℕ → ℝ) (P : Finset (Fin Q.R))
    (hd : ∀ s p, Q'.deg s p = Q.degOn P s p) :
    Q'.Fh h = (Q.Fon h .man P + Q.Fon h .woman P) / 2 := by
  unfold Member.Fh
  rw [Finset.sum_add_distrib, sum_dL Q' (W h) .man, sum_dL Q' (W h) .woman, sum_Fon, sum_Fon]
  simp only [hd]
  ring

theorem pLoss_pos (Q : Member n) (h : ℕ → ℝ) (hh : IsAdmissible h) (i : Fin Q.R)
    (v : Fin n) (hv : Q.moves .man i v) :
    0 < Q.pStar h i := by
  have key : ∀ s, 0 ≤ Q.pLoss h s i := by
    intro s
    unfold Member.pLoss
    rw [sum_Fon, sum_Fon, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun p _ => ?_
    have : Q.degOn (Finset.univ \ Q.down i) s p ≤ Q.degOn Finset.univ s p :=
      Finset.card_le_card (Finset.inter_subset_inter_right (Finset.sdiff_subset))
    linarith [W_mono h hh this]
  have hi : i ∈ Q.down i := by
    simp only [Member.down, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  have strict : 0 < Q.pLoss h .man i := by
    unfold Member.pLoss
    rw [sum_Fon, sum_Fon, ← Finset.sum_sub_distrib]
    refine Finset.sum_pos' (fun p _ => ?_) ⟨v, Finset.mem_univ _, ?_⟩
    · have : Q.degOn (Finset.univ \ Q.down i) .man p ≤ Q.degOn Finset.univ .man p :=
        Finset.card_le_card (Finset.inter_subset_inter_right (Finset.sdiff_subset))
      linarith [W_mono h hh this]
    · have : Q.degOn (Finset.univ \ Q.down i) .man v < Q.degOn Finset.univ .man v := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.inter_subset_inter_right (Finset.sdiff_subset))]
        refine ⟨i, ?_, ?_⟩
        · simp [Member.chainOf, hv]
        · simp [hi]
      linarith [W_lt h hh this]
  unfold Member.pStar
  linarith [key .woman]

theorem exp_le_of_lam {p q : ℝ} (hp : 0 < p) (h : lam p ≤ q) :
    Real.exp (-p) + Real.exp (-q) ≤ 1 := by
  unfold lam at h
  have h1 : 0 < 1 - Real.exp (-p) := by
    have : Real.exp (-p) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  have h2 : Real.log (1 - Real.exp (-p)) ≥ -q := by linarith
  have h3 : Real.exp (-q) ≤ 1 - Real.exp (-p) := by
    have := Real.exp_le_exp.mpr h2
    rwa [Real.exp_log h1] at this
  linarith

end Dev.T2

theorem chk_theorem_2 {n : ℕ} (h : ℕ → ℝ) (hh : IsAdmissible h) :
    IsBranchingPotential (fun Q : Member n => Q.R) (fun Q => Q.J) (fun Q => Q.Fh h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- an empty member, from Lemma 2.4 with no steps
    obtain ⟨I, hI, hch, -, -⟩ := lemma_2_4 (n := n) (R := 0) (fun _ => Equiv.refl _)
      (fun i => i.elim0) (fun v i j k hij hjk _ => by
        have : i = j := Fin.ext (by omega)
        subst this; rfl)
      (fun w i j k hij hjk _ => by
        have : i = j := Fin.ext (by omega)
        subst this; rfl)
    exact ⟨⟨I, 0, fun _ => Equiv.refl _, hI, hch⟩, rfl⟩
  · intro Q
    unfold Member.Fh
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun v _ => ?_)
    exact add_nonneg (Dev.T2.W_nonneg h hh _) (Dev.T2.W_nonneg h hh _)
  · intro Q hR
    have hR : Q.R = 0 := hR
    haveI : IsEmpty (Fin Q.R) := ⟨fun i => by have := i.2; omega⟩
    have hd : ∀ s v, Q.dL s v = 0 := by
      intro s v
      unfold Member.dL Member.deg Member.chainOf
      simp
    unfold Member.Fh
    simp [hd, W]
  · intro Q hR
    have hR : Q.R ≠ 0 := hR
    have hRpos : 0 < Q.R := Nat.pos_of_ne_zero hR
    -- a man moves in step 0
    set i₀ : Fin Q.R := ⟨0, hRpos⟩
    obtain ⟨v₀, hv₀⟩ : ∃ v, Q.moves .man i₀ v := by
      have hc := (Q.chain.2.2 i₀)
      have hne := hc.2.2.1.2
      by_contra hcon
      push_neg at hcon
      apply hne
      refine Equiv.ext fun v => ?_
      have := hcon v
      simpa [Member.moves] using this
    have hV : v₀ ∈ Q.V := by
      unfold Member.V
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold Member.dL Member.deg Member.chainOf Member.person
      apply Finset.card_pos.mpr
      exact ⟨i₀, by simp [hv₀]⟩
    have hBC := proposition_4_2 h hh Q hR
    obtain ⟨v, hv, hlt⟩ : ∃ v ∈ Q.V, Q.atFirst (fun i => lam (Q.pStar h i)) v ≤
        Q.atFirst (Q.qStar h) v := by
      by_contra hcon
      push_neg at hcon
      exact absurd hBC (not_le.mpr (Finset.sum_lt_sum_of_nonempty ⟨v₀, hV⟩ hcon))
    set i := Q.first v hv with hi
    have hlam : lam (Q.pStar h i) ≤ Q.qStar h i := by
      simpa [Member.atFirst, hv, hi] using hlt
    have hmem : i ∈ Q.chainOf .man v := by
      exact Finset.min'_mem _ _
    have hmoves : Q.moves .man i v := by
      simpa [Member.chainOf] using hmem
    have hp := Dev.T2.pLoss_pos Q h hh i v hmoves
    have hexp := Dev.T2.exp_le_of_lam hp hlam
    obtain ⟨hJ, Q₁, Q₂, e₁, e₂, -, -, hJ₁, hJ₂, hd₁, hd₂⟩ := lemma_3_7 Q i
    have hiD : i ∈ Q.down i := by
      simp only [Member.down, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.ReflTransGen.refl
    have hiU : i ∈ Q.up i := by
      simp only [Member.up, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.ReflTransGen.refl
    have hR₁ : Q₁.R < Q.R := by
      have := Fintype.card_congr e₁
      simp only [Fintype.card_coe, Fintype.card_fin] at this
      rw [← this]
      have h2 : (Finset.univ \ Q.down i).card < (Finset.univ : Finset (Fin Q.R)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset)]
        exact ⟨i, Finset.mem_univ _, by simp [hiD]⟩
      simpa using h2
    have hR₂ : Q₂.R < Q.R := by
      have := Fintype.card_congr e₂
      simp only [Fintype.card_coe, Fintype.card_fin] at this
      rw [← this]
      have h2 : (Finset.univ \ Q.up i).card < (Finset.univ : Finset (Fin Q.R)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.sdiff_subset)]
        exact ⟨i, Finset.mem_univ _, by simp [hiU]⟩
      simpa using h2
    refine ⟨Q₁, Q₂, hR₁, hR₂, by simpa [hJ₁, hJ₂] using hJ, ?_⟩
    have F1 := Dev.T2.Fh_of_deg Q Q₁ h _ hd₁
    have F2 := Dev.T2.Fh_of_deg Q Q₂ h _ hd₂
    have F0 := Dev.T2.Fh_eq Q h
    have e1 : Q₁.Fh h = Q.Fh h - Q.pStar h i := by
      rw [F1, F0]; unfold Member.pStar Member.pLoss; ring
    have e2 : Q₂.Fh h = Q.Fh h - Q.qStar h i := by
      rw [F2, F0]; unfold Member.qStar Member.qLoss; ring
    show Real.exp (Q₁.Fh h) + Real.exp (Q₂.Fh h) ≤ Real.exp (Q.Fh h)
    rw [e1, e2, sub_eq_add_neg, sub_eq_add_neg, Real.exp_add, Real.exp_add]
    have := Real.exp_pos (Q.Fh h)
    nlinarith

end StableCount
end

theorem solution : type_of% @StableCount.chk_theorem_2 := @StableCount.chk_theorem_2
