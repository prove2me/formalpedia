-- Prove2me | solution 1 for RunwayCPS.Makespan.min_makespan_dp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T22:01:24.637213+00:00
-- url     : https://prove2.me/submissions/f40cabcf-1a14-4a19-a5fe-58da403c4525

import Mathlib
import Definitions.Def_RunwayCPS_Makespan_DP

set_option autoImplicit false

namespace RunwayCPS.Makespan.P81b79bcc

open RunwayCPS.Makespan

variable {n : ℕ}

lemma mem_GNodes (I : Instance n) (p : ℕ) (w : List (Fin n)) :
    w ∈ GNodes I p ↔ IsGNode I p w := by
  unfold GNodes stageNodes
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · intro h; exact h.2
  · intro h
    refine ⟨⟨?_, h.1⟩, h⟩
    have hl := h.1.1
    rw [Finset.mem_image]
    refine ⟨fun i => w[i.1]'(by omega), Finset.mem_univ _, ?_⟩
    apply List.ext_getElem (by simp [hl]) (fun m h1 h2 => by simp)

/-- the window list of the sequence `σ` at (0-based) stage `s`, i.e. the stage-`s+1` node. -/
def win (k : ℕ) (σ : Fin n → Fin n) (s : ℕ) : List (Fin n) :=
  ((List.ofFn σ).take (s + 1)).drop (s + 1 - min (2 * k + 1) (s + 1))

lemma win_length (k : ℕ) (σ : Fin n → Fin n) (s : ℕ) (hs : s < n) :
    (win k σ s).length = min (2 * k + 1) (s + 1) := by
  simp [win]; omega

lemma win_getElem (k : ℕ) (σ : Fin n → Fin n) (s : ℕ) (m : ℕ) (hm : m < (win k σ s).length) :
    ∀ p : Fin n, (p : ℕ) = s + 1 - min (2 * k + 1) (s + 1) + m → (win k σ s)[m] = σ p := by
  intro p hp
  simp only [win, List.getElem_drop, List.getElem_take, List.getElem_ofFn]
  congr 1
  exact Fin.ext hp.symm

lemma getElem?_last {α : Type*} (w : List α) (d : α) (h : 0 < w.length) :
    w[w.length - 1]? = some (w.getLastD d) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rfl

lemma final_win [NeZero n] (k : ℕ) (σ : Fin n → Fin n) (s : ℕ) (hs : s < n) :
    final (win k σ s) = σ ⟨s, hs⟩ := by
  have hl := win_length k σ s hs
  have h1 := getElem?_last (win k σ s) (default : Fin n) (by omega)
  rw [List.getElem?_eq_getElem (by omega),
    win_getElem k σ s ((win k σ s).length - 1) (by omega) ⟨s, hs⟩ (by simp only; omega)] at h1
  exact (Option.some.inj h1).symm

lemma path_of_perm [NeZero n] (I : Instance n) (σ : Fin n → Fin n) (hc : IsCPS I.k σ)
    (hp : RespectsPrec I.prec σ) :
    (∀ s, s < n → IsGNode I (s + 1) (win I.k σ s)) ∧
    (∀ s, s + 1 < n → IsArc I.k (s + 1) (win I.k σ s) (win I.k σ (s + 1))) := by
  obtain ⟨hbij, hadm⟩ := hc
  refine ⟨fun s hs => ⟨⟨win_length I.k σ s hs, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact (List.nodup_ofFn.mpr hbij.1).sublist
      ((List.drop_sublist _ _).trans (List.take_sublist _ _))
  · intro m
    have hl := win_length I.k σ s hs
    have hm := m.2
    rw [Fin.getElem_fin, win_getElem I.k σ s m m.2 ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m,
      by omega⟩ rfl]
    have := hadm ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m, by omega⟩
    have hidx : (((s + 1 - min (2 * I.k + 1) (s + 1) + (m : ℕ) : ℕ)) : ℤ)
        = entryPos (s + 1) (win I.k σ s) m := by
      unfold entryPos; push_cast; omega
    rw [← hidx]; exact this
  · intro xy hxy hv
    have hl := win_length I.k σ s hs
    have gx : ∀ (m : ℕ) (hm : m < (win I.k σ s).length),
        (win I.k σ s)[m] = σ ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m, by omega⟩ :=
      fun m hm => win_getElem I.k σ s m hm _ rfl
    rcases hv with ⟨m₁, m₂, hlt, hy, hx⟩ | ⟨m, ⟨hy, hpos⟩ | ⟨hx, hpos⟩⟩
    · rw [Fin.getElem_fin, gx m₁ m₁.2] at hy
      rw [Fin.getElem_fin, gx m₂ m₂.2] at hx
      have h1 := hp xy hxy _ _ hx hy
      rw [Fin.lt_def] at h1 hlt
      simp only at h1
      omega
    · have hm := m.2
      rw [Fin.getElem_fin, gx m m.2] at hy
      obtain ⟨px, hpx⟩ := hbij.2 xy.1
      have h1 := hp xy hxy px _ hpx hy
      have h2 := hadm px
      rw [hpx, abs_le] at h2
      rw [Fin.lt_def] at h1
      simp only at h1
      unfold entryPos at hpos
      omega
    · have hm := m.2
      rw [Fin.getElem_fin, gx m m.2] at hx
      obtain ⟨py, hpy⟩ := hbij.2 xy.2
      have h1 := hp xy hxy _ py hx hpy
      have h2 := hadm py
      rw [hpy, abs_le] at h2
      rw [Fin.lt_def] at h1
      simp only at h1
      unfold entryPos at hpos
      omega
  · intro s hs1
    unfold IsArc
    have hl := win_length I.k σ s (by omega)
    have hl1 := win_length I.k σ (s + 1) hs1
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]; omega
    · intro m h1 h2
      simp only [List.length_take, List.length_drop] at h1 h2
      rw [List.getElem_take, List.getElem_drop,
        win_getElem I.k σ (s + 1) m (by omega) ⟨s + 1 + 1 - min (2 * I.k + 1) (s + 1 + 1) + m,
          by omega⟩ rfl,
        win_getElem I.k σ s _ (by omega) ⟨s + 1 + 1 - min (2 * I.k + 1) (s + 1 + 1) + m,
          by omega⟩ (by simp only; omega)]

lemma perm_of_path [NeZero n] (I : Instance n) (hprec : ∀ xy ∈ I.prec, xy.1 ≠ xy.2)
    (v : ℕ → List (Fin n)) (hG : ∀ s, s < n → IsGNode I (s + 1) (v (s + 1)))
    (hA : ∀ s, s + 1 < n → IsArc I.k (s + 1) (v (s + 1)) (v (s + 1 + 1))) :
    IsCPS I.k (pathSeq v) ∧ RespectsPrec I.prec (pathSeq v) := by
  have hlen : ∀ s, s < n → (v (s + 1)).length = min (2 * I.k + 1) (s + 1) :=
    fun s hs => (hG s hs).1.1
  have key : ∀ s, s < n → ∀ m, m < min (2 * I.k + 1) (s + 1) → ∀ p : Fin n,
      (p : ℕ) = s + 1 - min (2 * I.k + 1) (s + 1) + m →
      (v (s + 1))[m]? = some (final (v ((p : ℕ) + 1))) := by
    intro s
    induction s with
    | zero =>
      intro hs m hm p hp
      have h0 := hlen 0 hs
      rw [show (p : ℕ) + 1 = 0 + 1 by omega]
      have := getElem?_last (v (0 + 1)) (default : Fin n) (by omega)
      rw [h0, show min (2 * I.k + 1) (0 + 1) - 1 = 0 by omega] at this
      rw [show m = 0 by omega]
      exact this
    | succ s ih =>
      intro hs m hm p hp
      have h1 := hlen (s + 1) hs
      have h0 := hlen s (by omega)
      have harc := hA s hs
      unfold IsArc at harc
      by_cases hmc : m < min (2 * I.k) (s + 1)
      · have e1 : (v (s + 1 + 1))[m]? = ((v (s + 1 + 1)).take (min (2 * I.k) (s + 1)))[m]? := by
          rw [List.getElem?_take_of_lt hmc]
        rw [e1, harc, List.getElem?_drop]
        exact ih (by omega) _ (by omega) p (by omega)
      · rw [show (p : ℕ) + 1 = s + 1 + 1 by omega, show m = (v (s + 1 + 1)).length - 1 by omega]
        exact getElem?_last _ (default : Fin n) (by omega)
  have node_get : ∀ s (hs : s < n) m (hm : m < min (2 * I.k + 1) (s + 1)) (p : Fin n),
      (p : ℕ) = s + 1 - min (2 * I.k + 1) (s + 1) + m →
      (v (s + 1))[m]'(by rw [hlen s hs]; exact hm) = final (v ((p : ℕ) + 1)) := by
    intro s hs m hm p hp
    have h := key s hs m hm p hp
    rw [List.getElem?_eq_getElem (by rw [hlen s hs]; exact hm)] at h
    exact Option.some.inj h
  have adm : ∀ s (hs : s < n) m (hm : m < min (2 * I.k + 1) (s + 1)) (p : Fin n),
      (p : ℕ) = s + 1 - min (2 * I.k + 1) (s + 1) + m →
      |((final (v ((p : ℕ) + 1)) : ℕ) : ℤ) - ((p : ℕ) : ℤ)| ≤ (I.k : ℤ) := by
    intro s hs m hm p hp
    have h := (hG s hs).1.2.2 ⟨m, by rw [hlen s hs]; exact hm⟩
    rw [Fin.getElem_fin, node_get s hs m hm p hp] at h
    have hidx : ((p : ℕ) : ℤ) = entryPos (s + 1) (v (s + 1)) m := by
      unfold entryPos; rw [hlen s hs]; push_cast; omega
    rw [hidx]; exact h
  have adm1 : ∀ p : Fin n, |((final (v ((p : ℕ) + 1)) : ℕ) : ℤ) - ((p : ℕ) : ℤ)| ≤ (I.k : ℤ) := by
    intro p
    exact adm p p.2 (min (2 * I.k + 1) (p + 1) - 1) (by omega) p (by omega)
  have finj : Function.Injective (pathSeq v) := by
    have aux : ∀ p q : Fin n, (p : ℕ) < q → final (v ((p : ℕ) + 1)) ≠ final (v ((q : ℕ) + 1)) := by
      intro p q hpq hfe
      have ap := adm1 p
      have aq := adm1 q
      rw [hfe] at ap
      rw [abs_le] at ap aq
      have hnd := (hG q q.2).1.2.1
      have hql := hlen q q.2
      have g1 := node_get q q.2 (min (2 * I.k + 1) (q + 1) - 1 - ((q : ℕ) - p)) (by omega) p
        (by omega)
      have g2 := node_get q q.2 (min (2 * I.k + 1) (q + 1) - 1) (by omega) q (by omega)
      rw [hfe, ← g2] at g1
      have := (List.Nodup.getElem_inj_iff hnd).mp g1
      omega
    intro p q hfe
    change final (v ((p : ℕ) + 1)) = final (v ((q : ℕ) + 1)) at hfe
    rcases lt_trichotomy (p : ℕ) q with h | h | h
    · exact absurd hfe (aux p q h)
    · exact Fin.ext h
    · exact absurd hfe.symm (aux q p h)
  refine ⟨⟨⟨finj, Finite.injective_iff_surjective.mp finj⟩, adm1⟩, ?_⟩
  intro xy hxy p q hfp hfq
  change final (v ((p : ℕ) + 1)) = xy.1 at hfp
  change final (v ((q : ℕ) + 1)) = xy.2 at hfq
  have hne := hprec xy hxy
  rw [Fin.lt_def]
  by_contra hcon
  have hne' : (p : ℕ) ≠ q := fun h => hne (by rw [← hfp, ← hfq, h])
  have hlt : (q : ℕ) < p := by omega
  have ax := adm1 p
  rw [hfp, abs_le] at ax
  by_cases hd : (p : ℕ) - q ≤ 2 * I.k
  · have hpl := hlen p p.2
    have g1 := node_get p p.2 (min (2 * I.k + 1) (p + 1) - 1 - ((p : ℕ) - q)) (by omega)
      q (by omega)
    have g2 := node_get p p.2 (min (2 * I.k + 1) (p + 1) - 1) (by omega) p (by omega)
    rw [hfq] at g1
    rw [hfp] at g2
    refine (hG p p.2).2 xy hxy (Or.inl ⟨⟨min (2 * I.k + 1) (p + 1) - 1 - ((p : ℕ) - q), by omega⟩,
      ⟨min (2 * I.k + 1) (p + 1) - 1, by omega⟩, ?_, g1, g2⟩)
    simp only [Fin.mk_lt_mk]
    omega
  · have hql := hlen q q.2
    have g1 := node_get q q.2 (min (2 * I.k + 1) (q + 1) - 1) (by omega) q (by omega)
    rw [hfq] at g1
    refine (hG q q.2).2 xy hxy (Or.inr ⟨⟨min (2 * I.k + 1) (q + 1) - 1, by omega⟩, Or.inl ⟨g1, ?_⟩⟩)
    unfold entryPos
    simp only [hql]
    omega

lemma isLeast_iff_of (S1 S2 : Set ℝ) (sub : S2 ⊆ S1) (low : ∀ x ∈ S1, ∃ y ∈ S2, y ≤ x)
    (D : ℝ) : IsLeast S1 D ↔ IsLeast S2 D := by
  constructor
  · rintro ⟨hD1, hlb⟩
    obtain ⟨y, hy, hyD⟩ := low D hD1
    have := hlb (sub hy)
    have hyD' : y = D := le_antisymm hyD this
    exact ⟨hyD' ▸ hy, fun z hz => hlb (sub hz)⟩
  · rintro ⟨hD2, hlb⟩
    refine ⟨sub hD2, fun x hx => ?_⟩
    obtain ⟨y, hy, hyx⟩ := low x hx
    exact (hlb hy).trans hyx

lemma T_one [NeZero n] (I : Instance n) (j : List (Fin n)) :
    T I 1 j = ((I.e (final j) : ℝ) : WithTop ℝ) := by
  rfl

lemma T_succ [NeZero n] (I : Instance n) (p : ℕ) (j : List (Fin n)) :
    T I (p + 2) j = max ((I.e (final j) : ℝ) : WithTop ℝ)
        (((GNodes I (p + 1)).filter
            (fun i => IsArc I.k (p + 1) i j ∧ T I (p + 1) i ≤ ((I.l (final i) : ℝ) : WithTop ℝ))).inf
          (fun i => T I (p + 1) i + ((I.δ (final i) (final j) : ℝ) : WithTop ℝ))) := by
  rw [T]

lemma max_inf_attain {ι : Type*} (S : Finset ι) (F : ι → WithTop ℝ) (a x : ℝ)
    (h : max (a : WithTop ℝ) (S.inf F) = (x : WithTop ℝ)) : a ≤ x ∧ ∃ i ∈ S, F i ≤ (x : WithTop ℝ) := by
  have h1 := le_max_left (a : WithTop ℝ) (S.inf F)
  have h2 := le_max_right (a : WithTop ℝ) (S.inf F)
  rw [h] at h1 h2
  refine ⟨by exact_mod_cast h1, ?_⟩
  have hne : S.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc, Finset.inf_empty] at h2
    exact WithTop.not_top_le_coe x h2
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf S hne F
  exact ⟨i, hi, he ▸ h2⟩

lemma lower [NeZero n] (I : Instance n) :
    ∀ p : ℕ, ∀ j τ, τ ∈ arrivals I (p + 1) j → T I (p + 1) j ≤ (τ : WithTop ℝ) := by
  intro p
  induction p with
  | zero =>
    intro j τ h
    obtain ⟨v, t, hG, hA, hvj, hW, he, hS, hτ⟩ := h
    show T I 1 j ≤ _
    rw [T_one, hτ]; exact_mod_cast he
  | succ p ih =>
    intro j τ h
    obtain ⟨v, t, hG, hA, hvj, hW, he, hS, hτ⟩ := h
    show T I (p + 2) j ≤ _
    rw [T_succ, hτ]
    apply max_le (by exact_mod_cast he)
    have hwin := hW (p + 1) (by omega) (by omega)
    have hT1 : T I (p + 1) (v (p + 1)) ≤ ((t (p + 1) : ℝ) : WithTop ℝ) :=
      ih (v (p + 1)) (t (p + 1)) ⟨v, t, fun q h1 h2 => hG q h1 (by omega),
        fun q h1 h2 => hA q h1 (by omega), rfl, fun q h1 h2 => hW q h1 (by omega), hwin.1,
        fun q r h1 h2 h3 => hS q r h1 h2 (by omega), rfl⟩
    have hi : v (p + 1) ∈ (GNodes I (p + 1)).filter
        (fun i => IsArc I.k (p + 1) i j ∧ T I (p + 1) i ≤ ((I.l (final i) : ℝ) : WithTop ℝ)) := by
      rw [Finset.mem_filter]
      refine ⟨(mem_GNodes I _ _).mpr (hG (p + 1) (by omega) (by omega)), ?_, ?_⟩
      · have := hA (p + 1) (by omega) (by omega)
        rwa [hvj] at this
      · exact hT1.trans (by exact_mod_cast hwin.2)
    have hsep := hS (p + 1) (p + 1 + 1) (by omega) (by omega) (le_refl _)
    rw [hvj] at hsep
    calc _ ≤ T I (p + 1) (v (p + 1)) + ((I.δ (final (v (p + 1))) (final j) : ℝ) : WithTop ℝ) :=
          by exact Finset.inf_le hi
      _ ≤ ((t (p + 1) : ℝ) : WithTop ℝ) + ((I.δ (final (v (p + 1))) (final j) : ℝ) : WithTop ℝ) :=
          add_le_add_left hT1 _
      _ = ((t (p + 1) + I.δ (final (v (p + 1))) (final j) : ℝ) : WithTop ℝ) :=
          (WithTop.coe_add _ _).symm
      _ ≤ ((t (p + 1 + 1) : ℝ) : WithTop ℝ) := WithTop.coe_le_coe.mpr (by linarith)

lemma attain [NeZero n] (I : Instance n) : ∀ p : ℕ, ∀ j, IsGNode I (p + 1) j → ∀ x : ℝ,
    T I (p + 1) j = (x : WithTop ℝ) →
    ∃ (v : ℕ → List (Fin n)) (t : ℕ → ℝ),
      (∀ q, 1 ≤ q → q ≤ p + 1 → IsGNode I q (v q)) ∧
      (∀ q, 1 ≤ q → q < p + 1 → IsArc I.k q (v q) (v (q + 1))) ∧
      v (p + 1) = j ∧
      (∀ q, 1 ≤ q → q < p + 1 → I.e (final (v q)) ≤ t q ∧ t q ≤ I.l (final (v q))) ∧
      I.e (final j) ≤ t (p + 1) ∧
      (∀ q, 1 ≤ q → q < p + 1 → I.δ (final (v q)) (final (v (q + 1))) ≤ t (q + 1) - t q) ∧
      t (p + 1) = x := by
  intro p
  induction p with
  | zero =>
    intro j hj x hx
    have hx' : T I 1 j = (x : WithTop ℝ) := hx
    rw [T_one] at hx'
    have hex : I.e (final j) = x := by exact_mod_cast hx'
    refine ⟨fun _ => j, fun _ => x, ?_, fun q h1 h2 => by omega, rfl,
      fun q h1 h2 => by omega, le_of_eq hex, fun q h1 h2 => by omega, rfl⟩
    intro q h1 h2
    obtain rfl : q = 1 := by omega
    exact hj
  | succ p ih =>
    intro j hj x hx
    have hx' : T I (p + 2) j = (x : WithTop ℝ) := hx
    rw [T_succ] at hx'
    obtain ⟨hex, i, hi, hFi⟩ := max_inf_attain _ _ _ _ hx'
    rw [Finset.mem_filter] at hi
    obtain ⟨hiG, hiA, hiT⟩ := hi
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hiT)
    rw [← hy] at hiT hFi
    have hyl : y ≤ I.l (final i) := by exact_mod_cast hiT
    rw [← WithTop.coe_add] at hFi
    have hyx : y + I.δ (final i) (final j) ≤ x := by exact_mod_cast hFi
    obtain ⟨v, t, hG, hA, hvi, hW, he, hS, hty⟩ :=
      ih i ((mem_GNodes I _ _).mp hiG) y hy.symm
    refine ⟨fun q => if q = p + 1 + 1 then j else v q, fun q => if q = p + 1 + 1 then x else t q,
      ?_, ?_, by simp, ?_, by simpa using hex, ?_, by simp⟩
    · intro q h1 h2
      by_cases hq : q = p + 1 + 1
      · simp only [if_pos hq]; rw [hq]; exact hj
      · simp only [if_neg hq]; exact hG q h1 (by omega)
    · intro q h1 h2
      by_cases hq : q = p + 1
      · subst hq
        simp only [show p + 1 ≠ p + 1 + 1 by omega, if_false, if_true]
        rw [hvi]; exact hiA
      · simp only [show q ≠ p + 1 + 1 by omega, show q + 1 ≠ p + 1 + 1 by omega, if_false]
        exact hA q h1 (by omega)
    · intro q h1 h2
      by_cases hq : q = p + 1
      · subst hq
        simp only [show p + 1 ≠ p + 1 + 1 by omega, if_false]
        rw [hvi, hty]
        exact ⟨hty ▸ he, hyl⟩
      · simp only [show q ≠ p + 1 + 1 by omega, if_false]
        exact hW q h1 (by omega)
    · intro q h1 h2
      by_cases hq : q = p + 1
      · subst hq
        simp only [show p + 1 ≠ p + 1 + 1 by omega, if_false, if_true]
        rw [hvi, hty]
        linarith
      · simp only [show q ≠ p + 1 + 1 by omega, show q + 1 ≠ p + 1 + 1 by omega, if_false]
        exact hS q h1 (by omega)

lemma chain (I : Instance n) (htri : ∀ a b c, I.δ a c ≤ I.δ a b + I.δ b c)
    (a : ℕ → Fin n) (t : ℕ → ℝ) (N : ℕ)
    (h : ∀ q, 1 ≤ q → q < N → I.δ (a q) (a (q + 1)) ≤ t (q + 1) - t q) :
    ∀ q d, 1 ≤ q → q + 1 + d ≤ N → I.δ (a q) (a (q + 1 + d)) ≤ t (q + 1 + d) - t q := by
  intro q d
  induction d with
  | zero => intro h1 h2; simpa using h q h1 (by omega)
  | succ d ih =>
    intro h1 h2
    have e1 := ih h1 (by omega)
    have e2 := h (q + 1 + d) (by omega) (by omega)
    have e3 := htri (a q) (a (q + 1 + d)) (a (q + 1 + d + 1))
    show I.δ (a q) (a (q + 1 + d + 1)) ≤ t (q + 1 + d + 1) - t q
    linarith

lemma fwd [NeZero n] (I : Instance n) (σ : Fin n → Fin n) (t : Fin n → ℝ)
    (hf : IsFeasible I σ t) :
    ∃ j ∈ GNodes I n, ∃ y : ℝ, T I n j = (y : WithTop ℝ) ∧ y ≤ makespan t ∧
      makespan t ≤ I.l (final j) := by
  obtain ⟨hc, hw, hs, hp⟩ := hf
  obtain ⟨hG, hA⟩ := path_of_perm I σ hc hp
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : n - 1 + 1 = n := by omega
  have hfinal : final (win I.k σ (n - 1)) = σ lastPos := final_win I.k σ (n - 1) (by omega)
  have hmem : makespan t ∈ arrivals I (n - 1 + 1) (win I.k σ (n - 1)) := by
    refine ⟨fun q => win I.k σ (q - 1), fun q => if h : q - 1 < n then t ⟨q - 1, h⟩ else 0,
      ?_, ?_, by simp, ?_, ?_, ?_, ?_⟩
    · intro q h1 h2
      have := hG (q - 1) (by omega)
      rwa [show q - 1 + 1 = q by omega] at this
    · intro q h1 h2
      have := hA (q - 1) (by omega)
      rw [show q - 1 + 1 = q by omega] at this
      show IsArc I.k q (win I.k σ (q - 1)) (win I.k σ (q + 1 - 1))
      rw [Nat.add_sub_cancel]; exact this
    · intro q h1 h2
      have hq : q - 1 < n := by omega
      show I.e (final (win I.k σ (q - 1))) ≤ (if h : q - 1 < n then t ⟨q - 1, h⟩ else 0) ∧
        (if h : q - 1 < n then t ⟨q - 1, h⟩ else 0) ≤ I.l (final (win I.k σ (q - 1)))
      rw [dif_pos hq, final_win I.k σ (q - 1) hq]
      exact hw ⟨q - 1, hq⟩
    · show I.e (final (win I.k σ (n - 1))) ≤
        (if h : n - 1 + 1 - 1 < n then t ⟨n - 1 + 1 - 1, h⟩ else 0)
      rw [dif_pos (by omega), hfinal]
      exact (hw lastPos).1
    · intro q r h1 h2 h3
      have hq : q - 1 < n := by omega
      have hr : r - 1 < n := by omega
      show I.δ (final (win I.k σ (q - 1))) (final (win I.k σ (r - 1))) ≤
        (if h : r - 1 < n then t ⟨r - 1, h⟩ else 0) - (if h : q - 1 < n then t ⟨q - 1, h⟩ else 0)
      rw [dif_pos hq, dif_pos hr, final_win I.k σ (q - 1) hq, final_win I.k σ (r - 1) hr]
      exact hs ⟨q - 1, hq⟩ ⟨r - 1, hr⟩ (by rw [Fin.mk_lt_mk]; omega)
    · show t lastPos = (if h : n - 1 + 1 - 1 < n then t ⟨n - 1 + 1 - 1, h⟩ else 0)
      rw [dif_pos (by omega)]
      rfl
  have hlow := lower I (n - 1) _ _ hmem
  rw [hn1] at hlow
  obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hlow)
  have hjG := hG (n - 1) (by omega)
  rw [hn1] at hjG
  refine ⟨win I.k σ (n - 1), (mem_GNodes I _ _).mpr hjG, y, hy.symm, ?_, ?_⟩
  · rw [← hy] at hlow; exact_mod_cast hlow
  · rw [hfinal]; exact (hw lastPos).2

lemma bwd [NeZero n] (I : Instance n) (htri : ∀ a b c, I.δ a c ≤ I.δ a b + I.δ b c)
    (hprec : ∀ xy ∈ I.prec, xy.1 ≠ xy.2) (j : List (Fin n)) (hj : j ∈ GNodes I n) (x : ℝ)
    (hx : T I n j = (x : WithTop ℝ)) (hxl : x ≤ I.l (final j)) :
    ∃ σ t, IsFeasible I σ t ∧ makespan t = x := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn1 : n - 1 + 1 = n := by omega
  obtain ⟨v, t, hG, hA, hvj, hW, he, hS, htx⟩ :=
    attain I (n - 1) j (by rw [hn1]; exact (mem_GNodes I _ _).mp hj) x (by rw [hn1]; exact hx)
  rw [hn1] at hG hA hvj hW he hS htx
  obtain ⟨hc, hp⟩ := perm_of_path I hprec v (fun s hs => hG (s + 1) (by omega) (by omega))
    (fun s hs => hA (s + 1) (by omega) (by omega))
  refine ⟨pathSeq v, fun p => t ((p : ℕ) + 1), ⟨hc, ?_, ?_, hp⟩, ?_⟩
  · intro p
    show I.e (final (v ((p : ℕ) + 1))) ≤ t ((p : ℕ) + 1) ∧
      t ((p : ℕ) + 1) ≤ I.l (final (v ((p : ℕ) + 1)))
    by_cases hp1 : (p : ℕ) + 1 < n
    · exact hW _ (by omega) hp1
    · have h' : (p : ℕ) + 1 = n := by omega
      rw [h', hvj, htx]
      exact ⟨htx ▸ he, hxl⟩
  · intro p q hpq
    have hpq' : (p : ℕ) < q := hpq
    have := chain I htri (fun q => final (v q)) t n hS ((p : ℕ) + 1) ((q : ℕ) - p - 1)
      (by omega) (by omega)
    rw [show (p : ℕ) + 1 + 1 + ((q : ℕ) - p - 1) = (q : ℕ) + 1 by omega] at this
    exact this
  · show t ((lastPos : Fin n) + 1) = x
    show t (n - 1 + 1) = x
    rw [hn1, htx]

end RunwayCPS.Makespan.P81b79bcc

open RunwayCPS.Makespan in
theorem solution {n : ℕ} [NeZero n] (I : Instance n)
    (hδ : ∀ a b, 0 ≤ I.δ a b) (htri : ∀ a b c, I.δ a c ≤ I.δ a b + I.δ b c)
    (hprec : ∀ xy ∈ I.prec, xy.1 ≠ xy.2) :
    ((∃ σ t, IsFeasible I σ t) ↔
        ∃ j ∈ GNodes I n, T I n j ≤ ((I.l (final j) : ℝ) : WithTop ℝ)) ∧
    ∀ τ : ℝ,
      IsLeast {m : ℝ | ∃ σ t, IsFeasible I σ t ∧ m = makespan t} τ ↔
        IsLeast {m : ℝ | ∃ j ∈ GNodes I n, T I n j = (m : WithTop ℝ) ∧ m ≤ I.l (final j)} τ := by
  refine ⟨⟨?_, ?_⟩, fun τ => RunwayCPS.Makespan.P81b79bcc.isLeast_iff_of _ _ ?_ ?_ τ⟩
  · rintro ⟨σ, t, hf⟩
    obtain ⟨j, hj, y, hy, hym, hml⟩ := RunwayCPS.Makespan.P81b79bcc.fwd I σ t hf
    exact ⟨j, hj, by rw [hy]; exact_mod_cast hym.trans hml⟩
  · rintro ⟨j, hj, hjl⟩
    obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hjl)
    obtain ⟨σ, t, hf, -⟩ := RunwayCPS.Makespan.P81b79bcc.bwd I htri hprec j hj x hx.symm
      (by rw [← hx] at hjl; exact_mod_cast hjl)
    exact ⟨σ, t, hf⟩
  · rintro m ⟨j, hj, hT, hml⟩
    obtain ⟨σ, t, hf, hmk⟩ := RunwayCPS.Makespan.P81b79bcc.bwd I htri hprec j hj m hT hml
    exact ⟨σ, t, hf, hmk.symm⟩
  · rintro s ⟨σ, t, hf, rfl⟩
    obtain ⟨j, hj, y, hy, hym, hml⟩ := RunwayCPS.Makespan.P81b79bcc.fwd I σ t hf
    exact ⟨y, ⟨j, hj, hy, hym.trans hml⟩, hym⟩
