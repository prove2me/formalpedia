-- Prove2me | solution 1 for TypeICutMinimalPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:38.882043+00:00
-- url     : https://prove2.me/submissions/a35eb7bc-fcc9-46af-b77b-7fedc663b954

import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_TypeICutMinimalPair
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open Set
theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E)
    (hcl : IsClosedCurve γ) (δ ε : ℝ) (hδ : 0 < δ)
    (a₀ b₀ : ℝ) (ha₀ : a₀ ∈ Set.Icc (0 : ℝ) γ.len) (hb₀ : b₀ ∈ Set.Icc (0 : ℝ) γ.len)
    (hsep₀ : δ ≤ dGamma γ a₀ b₀)
    (hcon₀ : dist (γ.toFun a₀) (γ.toFun b₀) ≤ ε * dGamma γ a₀ b₀) :
    ∃ t t' : ℝ, t ∈ Set.Icc (0 : ℝ) γ.len ∧ t' ∈ Set.Icc (0 : ℝ) γ.len ∧
      δ ≤ dGamma γ t t' ∧
      dist (γ.toFun t) (γ.toFun t') ≤ ε * dGamma γ t t' ∧
      δ ≤ (if t ≤ t' then t' - t else (γ.len - t) + t') ∧
      (if t ≤ t' then t' - t else (γ.len - t) + t') ≤ γ.len / 2 ∧
      (∀ a ∈ Set.Icc (0 : ℝ) γ.len, ∀ b ∈ Set.Icc (0 : ℝ) γ.len,
        δ ≤ dGamma γ a b → dist (γ.toFun a) (γ.toFun b) ≤ ε * dGamma γ a b →
          (if t ≤ t' then t' - t else (γ.len - t) + t')
            ≤ (if a ≤ b then b - a else (γ.len - a) + b)) := by
-- BODY
  -- `dGamma` is the continuous function `min |a-b| (γ.len - |a-b|)` because `γ` is closed.
  have hd : ∀ a b : ℝ, dGamma γ a b = min |a - b| (γ.len - |a - b|) := by
    intro a b; simp only [dGamma, if_pos hcl]
  have hDcont : Continuous (fun p : ℝ × ℝ => min |p.1 - p.2| (γ.len - |p.1 - p.2|)) :=
    ((continuous_fst.sub continuous_snd).abs).min
      (continuous_const.sub ((continuous_fst.sub continuous_snd).abs))
  have hγc : Continuous γ.toFun := (CurveLipschitz γ).continuous
  have hGcont : Continuous (fun p : ℝ × ℝ => dist (γ.toFun p.1) (γ.toFun p.2)) :=
    (hγc.comp continuous_fst).dist (hγc.comp continuous_snd)
  -- Three elementary facts about `ℓ`.
  have hDle : ∀ a b : ℝ, min |a - b| (γ.len - |a - b|)
      ≤ (if a ≤ b then b - a else (γ.len - a) + b) := by
    intro a b
    by_cases hab : a ≤ b
    · rw [if_pos hab]
      refine le_trans (min_le_left _ _) ?_
      rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
      linarith
    · rw [if_neg hab]
      refine le_trans (min_le_right _ _) ?_
      rw [abs_of_nonneg (by linarith [not_le.mp hab] : (0:ℝ) ≤ a - b)]
      linarith
  have hsum : ∀ a b : ℝ, a ≠ b →
      (if a ≤ b then b - a else (γ.len - a) + b)
        + (if b ≤ a then a - b else (γ.len - b) + a) = γ.len := by
    intro a b hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [if_pos (le_of_lt hlt), if_neg (not_le.mpr hlt)]; ring
    · rw [if_neg (not_le.mpr hgt), if_pos (le_of_lt hgt)]; ring
  have hDeq : ∀ a b : ℝ, a ≠ b →
      (if a ≤ b then b - a else (γ.len - a) + b)
        ≤ (if b ≤ a then a - b else (γ.len - b) + a) →
      min |a - b| (γ.len - |a - b|) = (if a ≤ b then b - a else (γ.len - a) + b) := by
    intro a b hne hle
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [if_pos (le_of_lt hlt)] at hle ⊢
      rw [if_neg (not_le.mpr hlt)] at hle
      rw [abs_of_nonpos (by linarith : a - b ≤ 0)]
      rw [min_eq_left (by linarith)]
      ring
    · rw [if_neg (not_le.mpr hgt)] at hle ⊢
      rw [if_pos (le_of_lt hgt)] at hle
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
      rw [min_eq_right (by linarith)]
      ring
  -- The admissible set, and its compactness.
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ∈ Set.Icc (0 : ℝ) γ.len ∧ p.2 ∈ Set.Icc (0 : ℝ) γ.len ∧
      δ ≤ min |p.1 - p.2| (γ.len - |p.1 - p.2|) ∧
      dist (γ.toFun p.1) (γ.toFun p.2) ≤ ε * min |p.1 - p.2| (γ.len - |p.1 - p.2|)} with hSdef
  have hmemS : ∀ p : ℝ × ℝ, p ∈ S ↔ (p.1 ∈ Set.Icc (0 : ℝ) γ.len ∧ p.2 ∈ Set.Icc (0 : ℝ) γ.len ∧
      δ ≤ min |p.1 - p.2| (γ.len - |p.1 - p.2|) ∧
      dist (γ.toFun p.1) (γ.toFun p.2) ≤ ε * min |p.1 - p.2| (γ.len - |p.1 - p.2|)) :=
    fun _ => Iff.rfl
  have hSeq : S = ((Set.Icc (0 : ℝ) γ.len) ×ˢ (Set.Icc (0 : ℝ) γ.len)) ∩
      ({p : ℝ × ℝ | δ ≤ min |p.1 - p.2| (γ.len - |p.1 - p.2|)} ∩
       {p : ℝ × ℝ | dist (γ.toFun p.1) (γ.toFun p.2)
          ≤ ε * min |p.1 - p.2| (γ.len - |p.1 - p.2|)}) := by
    ext p
    simp only [hmemS p, Set.mem_inter_iff, Set.mem_prod]
    tauto
  have hScompact : IsCompact S := by
    rw [hSeq]
    refine (isCompact_Icc.prod isCompact_Icc).inter_right ?_
    exact (isClosed_le continuous_const hDcont).inter
      (isClosed_le hGcont (continuous_const.mul hDcont))
  have hSne : S.Nonempty := by
    refine ⟨(a₀, b₀), ?_⟩
    rw [hmemS]
    refine ⟨ha₀, hb₀, ?_, ?_⟩
    · rw [← hd]; exact hsep₀
    · rw [← hd]; exact hcon₀
  obtain ⟨q, hqS, hqmin⟩ := hScompact.exists_isMinOn hSne hDcont.continuousOn
  have hqmin' : ∀ p ∈ S, min |q.1 - q.2| (γ.len - |q.1 - q.2|)
      ≤ min |p.1 - p.2| (γ.len - |p.1 - p.2|) := isMinOn_iff.mp hqmin
  obtain ⟨hq1, hq2, hqsep, hqcon⟩ := (hmemS q).mp hqS
  have hqne : q.1 ≠ q.2 := by
    intro hEq
    have : |q.1 - q.2| = 0 := by rw [hEq]; simp
    have h1 : δ ≤ |q.1 - q.2| := le_trans hqsep (min_le_left _ _)
    linarith
  -- The swapped pair lies in `S` too.
  have hswapmem : (q.2, q.1) ∈ S := by
    rw [hmemS]
    have habs : |q.2 - q.1| = |q.1 - q.2| := abs_sub_comm _ _
    refine ⟨hq2, hq1, ?_, ?_⟩
    · simpa [habs] using hqsep
    · simpa [habs, dist_comm] using hqcon
  -- Pick whichever of `(q.1,q.2)`, `(q.2,q.1)` has the shorter counter-clockwise arc.
  have key : ∀ u v : ℝ, (u, v) ∈ S → (v, u) ∈ S → u ≠ v →
      min |u - v| (γ.len - |u - v|) = min |q.1 - q.2| (γ.len - |q.1 - q.2|) →
      (if u ≤ v then v - u else (γ.len - u) + v)
        ≤ (if v ≤ u then u - v else (γ.len - v) + u) →
      ∃ t t' : ℝ, t ∈ Set.Icc (0 : ℝ) γ.len ∧ t' ∈ Set.Icc (0 : ℝ) γ.len ∧
        δ ≤ dGamma γ t t' ∧
        dist (γ.toFun t) (γ.toFun t') ≤ ε * dGamma γ t t' ∧
        δ ≤ (if t ≤ t' then t' - t else (γ.len - t) + t') ∧
        (if t ≤ t' then t' - t else (γ.len - t) + t') ≤ γ.len / 2 ∧
        (∀ a ∈ Set.Icc (0 : ℝ) γ.len, ∀ b ∈ Set.Icc (0 : ℝ) γ.len,
          δ ≤ dGamma γ a b → dist (γ.toFun a) (γ.toFun b) ≤ ε * dGamma γ a b →
            (if t ≤ t' then t' - t else (γ.len - t) + t')
              ≤ (if a ≤ b then b - a else (γ.len - a) + b)) := by
    intro u v huv hvu hne hDq hshort
    obtain ⟨hu, hv, husep, hucon⟩ := (hmemS (u, v)).mp huv
    have hell : min |u - v| (γ.len - |u - v|) = (if u ≤ v then v - u else (γ.len - u) + v) :=
      hDeq u v hne hshort
    refine ⟨u, v, hu, hv, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hd]; exact husep
    · rw [hd]; exact hucon
    · rw [← hell]; exact husep
    · have hs := hsum u v hne
      linarith
    · intro a ha b hb hsep hcon
      have hmem : (a, b) ∈ S := by
        rw [hmemS]
        refine ⟨ha, hb, ?_, ?_⟩
        · rw [← hd]; exact hsep
        · rw [← hd]; exact hcon
      have h1 := hqmin' (a, b) hmem
      rw [← hell, hDq]
      exact le_trans h1 (hDle a b)
  rcases le_total (if q.1 ≤ q.2 then q.2 - q.1 else (γ.len - q.1) + q.2)
      (if q.2 ≤ q.1 then q.1 - q.2 else (γ.len - q.2) + q.1) with hle | hge
  · exact key q.1 q.2 hqS hswapmem hqne rfl hle
  · refine key q.2 q.1 hswapmem hqS (Ne.symm hqne) ?_ hge
    rw [abs_sub_comm]
