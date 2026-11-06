-- Prove2me | solution 1 for WhittFLT.Reflection.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:57:10.539244+00:00
-- url     : https://prove2.me/submissions/ea459889-388c-4bbc-9912-c91caa510be2

import Mathlib
import Definitions.Def_WhittFLT_Composition_SkorohodD
import Definitions.Def_WhittFLT_Reflection_Supremum
import Theorems.Thm_WhittFLT_Reflection_billingsley_lemma_1

open WhittFLT.Composition WhittFLT.Reflection
open Set Filter Topology Metric
open scoped ENNReal

namespace W61

lemma cadlag_mono {S : Type*} [MetricSpace S] {T T' : Set ℝ} {x : ℝ → S}
    (hx : IsCadlagOn T x) (h : T' ⊆ T) : IsCadlagOn T' x := by
  intro t ht
  obtain ⟨h1, l, hl⟩ := hx t (h ht)
  exact ⟨h1.mono (inter_subset_inter_left _ h), l,
    hl.mono_left (nhdsWithin_mono _ (inter_subset_inter_left _ h))⟩

lemma supDist_le_of {E : Type*} [PseudoMetricSpace E] (a b : ℝ) (f g : ℝ → E) (r : ℝ)
    (h : ∀ t ∈ Icc a b, dist (f t) (g t) ≤ r) : supDist a b f g ≤ ENNReal.ofReal r := by
  unfold supDist
  refine iSup₂_le fun t ht => ?_
  rw [edist_dist]; exact ENNReal.ofReal_le_ofReal (h t ht)

lemma dist_le_of_supDist_lt {E : Type*} [PseudoMetricSpace E] (a b : ℝ) (f g : ℝ → E) (r : ℝ)
    (h : supDist a b f g < ENNReal.ofReal r) : ∀ t ∈ Icc a b, dist (f t) (g t) < r := by
  intro t ht
  have : edist (f t) (g t) < ENNReal.ofReal r :=
    lt_of_le_of_lt (le_iSup₂ (f := fun t _ => edist (f t) (g t)) t ht) h
  rw [edist_dist] at this
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).1 this

lemma find_piece (k : ℕ) (u : Fin (k + 1) → ℝ) (hu : StrictMono u) (t : ℝ)
    (ht : t ∈ Ico (u 0) (u (Fin.last k))) :
    ∃ j : Fin k, u j.castSucc ≤ t ∧ t < u j.succ := by
  induction k with
  | zero => exact absurd ht.2 (not_lt.2 (by simp [Fin.last]; exact ht.1))
  | succ k ih =>
    by_cases h : t < u (Fin.castSucc (Fin.last k))
    · obtain ⟨j, hj1, hj2⟩ := ih (u ∘ Fin.castSucc) (hu.comp Fin.strictMono_castSucc)
        ⟨by simpa using ht.1, by simpa using h⟩
      refine ⟨j.castSucc, by simpa using hj1, ?_⟩
      rw [Fin.succ_castSucc]; simpa using hj2
    · push_neg at h
      exact ⟨Fin.last k, h, by rw [Fin.succ_last]; exact ht.2⟩

lemma cadlag_bdd (p q : ℝ) (hpq : p ≤ q) (x : ℝ → ℝ) (hx : IsCadlagOn (Icc p q) x) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ Icc p q, |x t| ≤ M := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    refine ⟨|x p|, abs_nonneg _, fun t ht => ?_⟩
    rw [le_antisymm ht.2 ht.1]
  · obtain ⟨n, t, ht0, htl, htm, hto⟩ := billingsley_lemma_1 p q h x hx 1 one_pos
    refine ⟨∑ i, |x (t i)| + 1, by positivity, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.2 with hsq | hsq
    · rw [hsq, ← htl]
      have := Finset.single_le_sum (f := fun i => |x (t i)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ (Fin.last n))
      linarith
    · obtain ⟨j, hj1, hj2⟩ := find_piece n t htm s ⟨by rw [ht0]; exact hs.1, by rw [htl]; exact hsq⟩
      have hmem1 : s ∈ Ico (t j.castSucc) (t j.succ) := ⟨hj1, hj2⟩
      have hmem2 : t j.castSucc ∈ Ico (t j.castSucc) (t j.succ) := ⟨le_rfl, lt_of_le_of_lt hj1 hj2⟩
      have hlt := lt_of_le_of_lt (le_trans
        (le_iSup₂ (f := fun s₂ _ => edist (x s) (x s₂)) _ hmem2)
        (le_iSup₂ (f := fun s₁ _ => ⨆ s₂ ∈ Ico (t j.castSucc)
          (t j.succ), edist (x s₁) (x s₂)) s hmem1)) (hto j)
      rw [edist_lt_ofReal, Real.dist_eq] at hlt
      have := Finset.single_le_sum (f := fun i => |x (t i)|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ j.castSucc)
      have h3 : |x s| ≤ |x s - x (t j.castSucc)| + |x (t j.castSucc)| := by
        have := abs_add_le (x s - x (t j.castSucc)) (x (t j.castSucc))
        simpa using this
      linarith


lemma image_Icc_of (p q : ℝ) (hpq : p ≤ q) (f : ℝ → ℝ) (hm : StrictMonoOn f (Icc p q))
    (hc : ContinuousOn f (Icc p q)) : f '' Icc p q = Icc (f p) (f q) := by
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨hm.monotoneOn ⟨le_rfl, hpq⟩ ht ht.1, hm.monotoneOn ht ⟨hpq, le_rfl⟩ ht.2⟩
  · exact intermediate_value_Icc hpq hc

lemma tc_zero (b : ℝ) (hb : 0 ≤ b) (l : ℝ → ℝ) (h : IsTimeChange 0 b l) : l 0 = 0 := by
  obtain ⟨hm, hc, him⟩ := h
  rw [image_Icc_of 0 b hb l hm hc] at him
  exact ((Icc_eq_Icc_iff (hm.monotoneOn ⟨le_rfl, hb⟩ ⟨hb, le_rfl⟩ hb)).1 him).1

lemma sSup_le_add (I : Set ℝ) (hI : I.Nonempty) (f g : ℝ → ℝ) (d : ℝ)
    (hg : BddAbove (g '' I)) (h : ∀ s ∈ I, f s ≤ g s + d) :
    sSup (f '' I) ≤ sSup (g '' I) + d := by
  apply csSup_le (hI.image f)
  rintro _ ⟨s, hs, rfl⟩
  have := le_csSup hg (mem_image_of_mem g hs)
  linarith [h s hs]

end W61

open W61 in
theorem solution (b : ℝ) (hb : 0 < b) (x y : ℝ → ℝ)
    (hx : WhittFLT.Composition.IsCadlagOn (Icc 0 b) x) (hy : WhittFLT.Composition.IsCadlagOn (Icc 0 b) y) :
    WhittFLT.Composition.j1Dist 0 b (runSup x) (runSup y) ≤ WhittFLT.Composition.j1Dist 0 b x y := by
  obtain ⟨Mx, -, hMx⟩ := cadlag_bdd 0 b hb.le x hx
  obtain ⟨My, -, hMy⟩ := cadlag_bdd 0 b hb.le y hy
  unfold j1Dist
  refine le_iInf₂ fun l hl => ?_
  refine (iInf₂_le l hl).trans (max_le_max le_rfl ?_)
  set D := supDist 0 b x (y ∘ l) with hD
  by_cases htop : D = ⊤
  · rw [htop]; exact le_top
  have hpt : ∀ s ∈ Icc 0 b, |x s - y (l s)| ≤ D.toReal := by
    intro s hs
    have h1 : edist (x s) ((y ∘ l) s) ≤ D :=
      le_iSup₂ (f := fun t _ => edist (x t) ((y ∘ l) t)) s hs
    rw [edist_dist, ← ENNReal.ofReal_toReal htop] at h1
    rw [← Real.dist_eq]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h1
  have hlmem : ∀ s ∈ Icc 0 b, l s ∈ Icc 0 b := fun s hs => hl.2.2 ▸ mem_image_of_mem l hs
  rw [← ENNReal.ofReal_toReal htop]
  refine supDist_le_of 0 b _ _ _ fun t ht => ?_
  have hI : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have himg : l '' Icc 0 t = Icc 0 (l t) := by
    rw [image_Icc_of 0 t ht.1 l (hl.1.mono hI) (hl.2.1.mono hI), tc_zero b hb.le l hl]
  have hne : (Icc (0:ℝ) t).Nonempty := ⟨0, le_rfl, ht.1⟩
  have hry : runSup y (l t) = sSup ((y ∘ l) '' Icc 0 t) := by
    unfold runSup; rw [image_comp, himg]
  have hbx : BddAbove (x '' Icc 0 t) := ⟨Mx, by
    rintro _ ⟨s, hs, rfl⟩; exact (abs_le.1 (hMx s (hI hs))).2⟩
  have hby : BddAbove ((y ∘ l) '' Icc 0 t) := ⟨My, by
    rintro _ ⟨s, hs, rfl⟩; exact (abs_le.1 (hMy (l s) (hlmem s (hI hs)))).2⟩
  have e1 := sSup_le_add (Icc 0 t) hne x (y ∘ l) D.toReal hby fun s hs => by
    have := abs_le.1 (hpt s (hI hs)); simp only [Function.comp]; linarith
  have e2 := sSup_le_add (Icc 0 t) hne (y ∘ l) x D.toReal hbx fun s hs => by
    have := abs_le.1 (hpt s (hI hs)); simp only [Function.comp]; linarith
  rw [Function.comp_apply, hry, Real.dist_eq, abs_le]
  unfold runSup
  constructor <;> linarith
