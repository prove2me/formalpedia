-- Prove2me | solution 1 for Rudin.ch06_product_integrable_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T13:28:47.254775+00:00
-- url     : https://prove2.me/submissions/cfba3aa4-7cd1-4e59-a3d8-7d0315d09e89

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_ch06_refinement
import Theorems.Thm_Rudin_ch06_riemann_criterion

open Filter Topology

namespace RudinProd

open Rudin

/-- The division points of a partition increase. -/
lemma px_mono {a b : ℝ} (P : Partition a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) :
    P.x i ≤ P.x j := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    simp [this]
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with h | h
    · have him : i ≤ m := Nat.lt_succ_iff.mp h
      exact le_trans (ih him (by omega)) (P.mono m (by omega))
    · have : i = m + 1 := le_antisymm hij h
      simp [this]

lemma px_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have := px_mono P (Nat.zero_le i) hi
    rwa [P.first] at this
  · have := px_mono P hi (le_refl P.n)
    rwa [P.last] at this

/-- The trivial partition `{a, b}`. -/
def trivialPartition {a b : ℝ} (hab : a ≤ b) : Partition a b where
  n := 1
  x := fun i => if i = 0 then a else b
  first := by norm_num
  last := by norm_num
  mono := by
    intro i hi
    have : i = 0 := by omega
    subst this
    norm_num
    exact hab

/-- Every partition has a refinement having `c` among its division points. -/
lemma exists_refinement_with_point {a b : ℝ} (P : Partition a b) (c : ℝ) (hc : c ∈ Set.Icc a b) :
    ∃ P' : Partition a b, Refines P' P ∧ ∃ k, ∃ _ : k ≤ P'.n, P'.x k = c := by
  classical
  have hex : ∃ j, c ≤ P.x j := ⟨P.n, by rw [P.last]; exact hc.2⟩
  set k := Nat.find hex with hkdef
  have hkspec : c ≤ P.x k := Nat.find_spec hex
  have hkmin : ∀ j, j < k → P.x j < c := fun j hj => lt_of_not_ge (Nat.find_min hex hj)
  have hkn : k ≤ P.n := Nat.find_min' hex (by rw [P.last]; exact hc.2)
  refine ⟨⟨P.n + 1, fun j => if j < k then P.x j else if j = k then c else P.x (j - 1), ?_, ?_, ?_⟩,
    ?_, k, ?_, ?_⟩
  · by_cases h : 0 < k
    · rw [if_pos h]
      exact P.first
    · have hk0 : k = 0 := by omega
      have hca : c ≤ a := by rw [← P.first, ← hk0]; exact hkspec
      rw [if_neg (by omega), if_pos (show 0 = k by omega)]
      exact le_antisymm hca hc.1
  · have h1 : ¬ (P.n + 1 < k) := by omega
    have h2 : ¬ (P.n + 1 = k) := by omega
    rw [if_neg h1, if_neg h2, Nat.add_sub_cancel]
    exact P.last
  · intro j hj
    rcases lt_trichotomy j k with h | h | h
    · rcases Nat.lt_or_ge (j + 1) k with h' | h'
      · have hjn : j < P.n := by omega
        rw [if_pos h, if_pos h']
        exact P.mono j hjn
      · have hjk : j + 1 = k := by omega
        have h2 : ¬ (j + 1 < k) := by omega
        rw [if_pos h, if_neg h2, if_pos hjk]
        exact le_of_lt (hkmin j h)
    · have h1 : ¬ (j < k) := by omega
      have h2 : ¬ (j + 1 < k) := by omega
      have h3 : ¬ (j + 1 = k) := by omega
      rw [if_neg h1, if_pos h, if_neg h2, if_neg h3, show j + 1 - 1 = k by omega]
      exact hkspec
    · have h1 : ¬ (j < k) := by omega
      have h1' : ¬ (j = k) := by omega
      have h2 : ¬ (j + 1 < k) := by omega
      have h3 : ¬ (j + 1 = k) := by omega
      rw [if_neg h1, if_neg h1', if_neg h2, if_neg h3, show j + 1 - 1 = j by omega]
      have hjn : j - 1 < P.n := by omega
      have := P.mono (j - 1) hjn
      have heq2 : j - 1 + 1 = j := by omega
      rwa [heq2] at this
  · intro i hi
    by_cases h : i < k
    · refine ⟨i, ?_, ?_⟩
      · show i ≤ P.n + 1
        omega
      · show (if i < k then P.x i else if i = k then c else P.x (i - 1)) = P.x i
        rw [if_pos h]
    · refine ⟨i + 1, ?_, ?_⟩
      · show i + 1 ≤ P.n + 1
        omega
      · show (if i + 1 < k then P.x (i + 1) else if i + 1 = k then c else P.x (i + 1 - 1)) = P.x i
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  · show k ≤ P.n + 1
    omega
  · show (if k < k then P.x k else if k = k then c else P.x (k - 1)) = c
    rw [if_neg (by omega), if_pos rfl]


/-- `Refines` is reflexive. -/
lemma Refines_refl {a b : ℝ} (P : Partition a b) : Refines P P :=
  fun i hi => ⟨i, hi, rfl⟩

/-- `Refines` is transitive. -/
lemma Refines_trans {a b : ℝ} {Q P' P : Partition a b} (h1 : Refines Q P') (h2 : Refines P' P) :
    Refines Q P := by
  intro i hi
  obtain ⟨j, hj, hxj⟩ := h2 i hi
  obtain ⟨k, hk, hxk⟩ := h1 j hj
  exact ⟨k, hk, by rw [hxk, hxj]⟩

/-- Any two partitions of `[a, b]` have a common refinement. -/
lemma exists_common_refinement {a b : ℝ} (P₁ P₂ : Partition a b) :
    ∃ Q : Partition a b, Refines Q P₁ ∧ Refines Q P₂ := by
  have key : ∀ k, k ≤ P₂.n + 1 →
      ∃ Q : Partition a b, Refines Q P₁ ∧ ∀ i < k, ∃ j ≤ Q.n, Q.x j = P₂.x i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨P₁, Refines_refl P₁, by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨Q, hQ1, hQ2⟩ := ih (by omega)
      have hmem : P₂.x m ∈ Set.Icc a b := px_mem P₂ (by omega)
      obtain ⟨Q', hQ'ref, j₀, hj₀, hxj₀⟩ := exists_refinement_with_point Q (P₂.x m) hmem
      refine ⟨Q', Refines_trans hQ'ref hQ1, ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i m with h | h
      · obtain ⟨j, hj, hxj⟩ := hQ2 i h
        obtain ⟨j', hj', hxj'⟩ := hQ'ref j hj
        exact ⟨j', hj', by rw [hxj', hxj]⟩
      · have : i = m := by omega
        subst this
        exact ⟨j₀, hj₀, hxj₀⟩
  obtain ⟨Q, hQ1, hQ2⟩ := key (P₂.n + 1) (le_refl _)
  exact ⟨Q, hQ1, fun i hi => hQ2 i (by omega)⟩

/-- On a subinterval, the oscillation of a product is controlled by the oscillations of the
factors. -/
lemma osc_mul_le {f g : ℝ → ℝ} {u v Mf Mg : ℝ} (huv : u ≤ v) (hMf0 : 0 ≤ Mf) (hMg0 : 0 ≤ Mg)
    (hMf : ∀ y ∈ Set.Icc u v, |f y| ≤ Mf) (hMg : ∀ y ∈ Set.Icc u v, |g y| ≤ Mg) :
    sSup ((fun x => f x * g x) '' Set.Icc u v) - sInf ((fun x => f x * g x) '' Set.Icc u v)
      ≤ Mg * (sSup (f '' Set.Icc u v) - sInf (f '' Set.Icc u v))
        + Mf * (sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) := by
  set K := Mg * (sSup (f '' Set.Icc u v) - sInf (f '' Set.Icc u v))
      + Mf * (sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) with hK
  have hnef : (f '' Set.Icc u v).Nonempty := ⟨f u, u, ⟨le_refl u, huv⟩, rfl⟩
  have hneg : (g '' Set.Icc u v).Nonempty := ⟨g u, u, ⟨le_refl u, huv⟩, rfl⟩
  have hnefg : ((fun x => f x * g x) '' Set.Icc u v).Nonempty := ⟨f u * g u, u, ⟨le_refl u, huv⟩, rfl⟩
  have hbddf : BddAbove (f '' Set.Icc u v) :=
    ⟨Mf, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hMf y hy)).2⟩
  have hbddf' : BddBelow (f '' Set.Icc u v) :=
    ⟨-Mf, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hMf y hy)).1⟩
  have hbddg : BddAbove (g '' Set.Icc u v) :=
    ⟨Mg, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hMg y hy)).2⟩
  have hbddg' : BddBelow (g '' Set.Icc u v) :=
    ⟨-Mg, by rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hMg y hy)).1⟩
  have hbddfg' : BddBelow ((fun x => f x * g x) '' Set.Icc u v) :=
    ⟨-(Mf * Mg), by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : |f y * g y| ≤ Mf * Mg := by
        rw [abs_mul]
        exact mul_le_mul (hMf y hy) (hMg y hy) (abs_nonneg _) hMf0
      exact (abs_le.mp h1).1⟩
  -- pointwise estimate
  have pointwise : ∀ s ∈ Set.Icc u v, ∀ t ∈ Set.Icc u v, f s * g s ≤ f t * g t + K := by
    intro s hs t ht
    have hfs : f s ≤ sSup (f '' Set.Icc u v) := le_csSup hbddf ⟨s, hs, rfl⟩
    have hft : sInf (f '' Set.Icc u v) ≤ f t := csInf_le hbddf' ⟨t, ht, rfl⟩
    have hgs : g s ≤ sSup (g '' Set.Icc u v) := le_csSup hbddg ⟨s, hs, rfl⟩
    have hgt : sInf (g '' Set.Icc u v) ≤ g t := csInf_le hbddg' ⟨t, ht, rfl⟩
    have hft' : f t ≤ sSup (f '' Set.Icc u v) := le_csSup hbddf ⟨t, ht, rfl⟩
    have hfs' : sInf (f '' Set.Icc u v) ≤ f s := csInf_le hbddf' ⟨s, hs, rfl⟩
    have hgt' : g t ≤ sSup (g '' Set.Icc u v) := le_csSup hbddg ⟨t, ht, rfl⟩
    have hgs' : sInf (g '' Set.Icc u v) ≤ g s := csInf_le hbddg' ⟨s, hs, rfl⟩
    have hgsb : |g s| ≤ Mg := hMg s hs
    have hftb : |f t| ≤ Mf := hMf t ht
    have hdecomp : f s * g s - f t * g t = (f s - f t) * g s + f t * (g s - g t) := by ring
    have h1 : (f s - f t) * g s ≤ Mg * (sSup (f '' Set.Icc u v) - sInf (f '' Set.Icc u v)) := by
      have hb1 : |f s - f t| ≤ sSup (f '' Set.Icc u v) - sInf (f '' Set.Icc u v) := by
        rw [abs_le]; constructor <;> linarith
      calc (f s - f t) * g s ≤ |(f s - f t) * g s| := le_abs_self _
        _ = |f s - f t| * |g s| := abs_mul _ _
        _ ≤ (sSup (f '' Set.Icc u v) - sInf (f '' Set.Icc u v)) * Mg :=
            mul_le_mul hb1 hgsb (abs_nonneg _) (le_trans (abs_nonneg _) hb1)
        _ = Mg * (sSup (f '' Set.Icc u v) - sInf (f '' Set.Icc u v)) := by ring
    have h2 : f t * (g s - g t) ≤ Mf * (sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) := by
      have hb2 : |g s - g t| ≤ sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v) := by
        rw [abs_le]; constructor <;> linarith
      calc f t * (g s - g t) ≤ |f t * (g s - g t)| := le_abs_self _
        _ = |f t| * |g s - g t| := abs_mul _ _
        _ ≤ Mf * (sSup (g '' Set.Icc u v) - sInf (g '' Set.Icc u v)) :=
            mul_le_mul hftb hb2 (abs_nonneg _) hMf0
    linarith [hdecomp]
  have step1 : ∀ t ∈ Set.Icc u v,
      sSup ((fun x => f x * g x) '' Set.Icc u v) ≤ f t * g t + K := by
    intro t ht
    refine csSup_le hnefg ?_
    rintro _ ⟨s, hs, rfl⟩
    exact pointwise s hs t ht
  have step2 : sSup ((fun x => f x * g x) '' Set.Icc u v)
      ≤ sInf ((fun x => f x * g x) '' Set.Icc u v) + K := by
    have : sSup ((fun x => f x * g x) '' Set.Icc u v) - K
        ≤ sInf ((fun x => f x * g x) '' Set.Icc u v) := by
      refine le_csInf hnefg ?_
      rintro _ ⟨t, ht, rfl⟩
      linarith [step1 t ht]
    linarith
  linarith


end RudinProd

open Rudin RudinProd in
/-- Rudin, Theorem 6.13(a), with the boundedness hypotheses of Chapter 6. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (f g α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hf : RSIntegrable a b f α) (hg : RSIntegrable a b g α)
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) (hgb : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M) :
    RSIntegrable a b (fun x => f x * g x) α := by
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨Mg, hMg⟩ := hgb
  have hMf0 : 0 ≤ Mf := le_trans (abs_nonneg _) (hMf a ⟨le_refl a, hab⟩)
  have hMg0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hMg a ⟨le_refl a, hab⟩)
  have hfgb : ∃ M, ∀ x ∈ Set.Icc a b, |f x * g x| ≤ M :=
    ⟨Mf * Mg, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hMf x hx) (hMg x hx) (abs_nonneg _) hMf0⟩
  rw [ch06_riemann_criterion a b hab (fun x => f x * g x) α hα hfgb]
  intro ε hε
  have hpos : 0 < Mf + Mg + 1 := by linarith
  set δ := ε / (Mf + Mg + 1) with hδ
  have hδpos : 0 < δ := div_pos hε hpos
  obtain ⟨P₁, hP₁⟩ := (ch06_riemann_criterion a b hab f α hα ⟨Mf, hMf⟩).mp hf δ hδpos
  obtain ⟨P₂, hP₂⟩ := (ch06_riemann_criterion a b hab g α hα ⟨Mg, hMg⟩).mp hg δ hδpos
  obtain ⟨Q, hQ1, hQ2⟩ := exists_common_refinement P₁ P₂
  have hrf := ch06_refinement a b hab f α hα ⟨Mf, hMf⟩ P₁ Q hQ1
  have hrg := ch06_refinement a b hab g α hα ⟨Mg, hMg⟩ P₂ Q hQ2
  have hQf : upperSum f α Q - lowerSum f α Q < δ := by linarith [hrf.1, hrf.2]
  have hQg : upperSum g α Q - lowerSum g α Q < δ := by linarith [hrg.1, hrg.2]
  refine ⟨Q, ?_⟩
  have expand : ∀ F : ℝ → ℝ, upperSum F α Q - lowerSum F α Q
      = ∑ i ∈ Finset.range Q.n, (sSup (F '' Set.Icc (Q.x i) (Q.x (i + 1)))
          - sInf (F '' Set.Icc (Q.x i) (Q.x (i + 1)))) * (α (Q.x (i + 1)) - α (Q.x i)) := by
    intro F
    rw [upperSum, lowerSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : upperSum (fun x => f x * g x) α Q - lowerSum (fun x => f x * g x) α Q
      ≤ Mg * (upperSum f α Q - lowerSum f α Q) + Mf * (upperSum g α Q - lowerSum g α Q) := by
    rw [expand, expand f, expand g, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i < Q.n := Finset.mem_range.mp hi
    have hle : Q.x i ≤ Q.x (i + 1) := Q.mono i hi'
    have hmem1 : Q.x i ∈ Set.Icc a b := px_mem Q (le_of_lt hi')
    have hmem2 : Q.x (i + 1) ∈ Set.Icc a b := px_mem Q hi'
    have hsub : Set.Icc (Q.x i) (Q.x (i + 1)) ⊆ Set.Icc a b := Set.Icc_subset_Icc hmem1.1 hmem2.2
    have hosc := osc_mul_le hle hMf0 hMg0 (fun y hy => hMf y (hsub hy)) (fun y hy => hMg y (hsub hy))
    have hΔ : 0 ≤ α (Q.x (i + 1)) - α (Q.x i) := by
      have := hα hmem1 hmem2 hle
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hosc hΔ]
  have hb1 : Mg * (upperSum f α Q - lowerSum f α Q) ≤ Mg * δ :=
    mul_le_mul_of_nonneg_left (le_of_lt hQf) hMg0
  have hb2 : Mf * (upperSum g α Q - lowerSum g α Q) ≤ Mf * δ :=
    mul_le_mul_of_nonneg_left (le_of_lt hQg) hMf0
  have hfin : (Mf + Mg) * δ < ε := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ hpos]
    nlinarith
  linarith
