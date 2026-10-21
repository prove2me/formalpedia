-- Prove2me | solution 1 for RunwayCPS.TotalDelay.min_total_delay_shortest_path
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T05:11:02.75599+00:00
-- url     : https://prove2.me/submissions/308b49c2-acc8-4149-9d8b-a46aad43eb82

import Mathlib
import Definitions.Def_RunwayCPS_TotalDelay_Network

set_option autoImplicit false

namespace RunwayCPS.TotalDelay.P14301573

open RunwayCPS.TotalDelay

variable {n : ℕ}

/-- separation between the aircraft at positions `p` and `q` (0 outside range). -/
noncomputable def e (I : Instance n) (σ : Fin n → Fin n) (p q : ℕ) : ℝ :=
  if h : p < n ∧ q < n then I.δ (σ ⟨p, h.1⟩) (σ ⟨q, h.2⟩) else 0

noncomputable def cost (I : Instance n) (σ : Fin n → Fin n) : ℝ :=
  ∑ s ∈ Finset.Ico 1 n, ((n : ℝ) - (s : ℝ)) * e I σ (s - 1) s

lemma sum_ident (g : ℕ → ℝ) (N : ℕ) :
    ∑ q ∈ Finset.range N, ∑ s ∈ Finset.Ico 1 (q + 1), g s
      = ∑ s ∈ Finset.Ico 1 N, ((N : ℝ) - (s : ℝ)) * g s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · simp only [Finset.sum_Ico_succ_top (by omega : 1 ≤ N)]
      have : ∑ s ∈ Finset.Ico 1 N, ((((N + 1 : ℕ) : ℝ)) - (s : ℝ)) * g s
          = ∑ s ∈ Finset.Ico 1 N, ((N : ℝ) - (s : ℝ)) * g s + ∑ s ∈ Finset.Ico 1 N, g s := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        push_cast; ring
      rw [this]
      push_cast; ring

lemma e_nonneg (I : Instance n) (hδ : ∀ a b : Fin n, 0 ≤ I.δ a b) (σ : Fin n → Fin n)
    (p q : ℕ) : 0 ≤ e I σ p q := by
  unfold e; split_ifs <;> simp [hδ]

lemma lower (I : Instance n) (σ : Fin n → Fin n) (t : Fin n → ℝ) (ht0 : ∀ p, 0 ≤ t p)
    (hsep : ∀ p q : Fin n, p < q → I.δ (σ p) (σ q) ≤ t q - t p) :
    cost I σ ≤ totalDelay t := by
  set T : ℕ → ℝ := fun p => if h : p < n then t ⟨p, h⟩ else 0 with hT
  have key : ∀ q, q < n → ∑ s ∈ Finset.Ico 1 (q + 1), e I σ (s - 1) s ≤ T q := by
    intro q
    induction q with
    | zero => intro h; simp [hT, h, ht0]
    | succ q ih =>
      intro h
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ q + 1)]
      have h1 := ih (by omega)
      have h2 := hsep ⟨q, by omega⟩ ⟨q + 1, h⟩ (by simp [Fin.lt_def])
      simp only [hT, dif_pos h, dif_pos (show q < n by omega), e] at h1 h2 ⊢
      simp only [Nat.add_sub_cancel, dif_pos (show q < n ∧ q + 1 < n from ⟨by omega, h⟩)]
      linarith
  have htd : totalDelay t = ∑ q ∈ Finset.range n, T q := by
    unfold totalDelay
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp [hT, p.2]
  rw [htd, cost, ← sum_ident (fun s => e I σ (s - 1) s) n]
  exact Finset.sum_le_sum (fun q hq => key q (Finset.mem_range.mp hq))

lemma greedy (I : Instance n) (hδ : ∀ a b : Fin n, 0 ≤ I.δ a b)
    (htri : ∀ a b c : Fin n, I.δ a c ≤ I.δ a b + I.δ b c) (σ : Fin n → Fin n) :
    ∃ t : Fin n → ℝ, (∀ p, 0 ≤ t p) ∧
      (∀ p q : Fin n, p < q → I.δ (σ p) (σ q) ≤ t q - t p) ∧ totalDelay t = cost I σ := by
  set T : ℕ → ℝ := fun q => ∑ s ∈ Finset.Ico 1 (q + 1), e I σ (s - 1) s with hT
  refine ⟨fun p => T p, fun p => Finset.sum_nonneg (fun s _ => e_nonneg I hδ σ _ _), ?_, ?_⟩
  · have step : ∀ q, T (q + 1) - T q = e I σ q (q + 1) := by
      intro q
      simp only [hT]
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ q + 1)]
      simp
    have ind : ∀ (p : ℕ) (d : ℕ), p + 1 + d < n → e I σ p (p + 1 + d) ≤ T (p + 1 + d) - T p := by
      intro p d
      induction d with
      | zero => intro _; exact (step p).ge
      | succ d ih =>
        intro h
        have h1 := ih (by omega)
        have h2 := step (p + 1 + d)
        have h3 : e I σ p (p + 1 + (d + 1)) ≤ e I σ p (p + 1 + d) + e I σ (p + 1 + d) (p + 1 + d + 1) := by
          unfold e
          rw [dif_pos ⟨by omega, by omega⟩, dif_pos ⟨by omega, by omega⟩,
            dif_pos ⟨by omega, by omega⟩]
          have := htri (σ ⟨p, by omega⟩) (σ ⟨p + 1 + d, by omega⟩) (σ ⟨p + 1 + d + 1, by omega⟩)
          convert this using 3
          all_goals (apply Fin.ext; simp only; omega)
        have h4 : p + 1 + (d + 1) = p + 1 + d + 1 := by omega
        rw [h4] at h3 ⊢
        linarith
    intro p q hpq
    have hq : (q : ℕ) = p + 1 + ((q : ℕ) - p - 1) := by
      have : (p : ℕ) < q := hpq
      omega
    have := ind p ((q : ℕ) - p - 1) (by rw [← hq]; exact q.2)
    rw [← hq] at this
    unfold e at this
    rw [dif_pos ⟨p.2, q.2⟩] at this
    exact this
  · unfold totalDelay cost
    rw [← sum_ident (fun s => e I σ (s - 1) s) n, ← Fin.sum_univ_eq_sum_range]

/-- the window list of the sequence `σ` at stage `s`. -/
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

lemma getLast?_of {α : Type*} (w : List α) (h : 0 < w.length) (a : α)
    (ha : w[w.length - 1]? = some a) : w.getLast? = some a := by
  rw [List.getLast?_eq_getElem?]; exact ha

lemma getElem?_last {α : Type*} (w : List α) (d : α) (h : 0 < w.length) :
    w[w.length - 1]? = some (w.getLastD d) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  rfl

lemma path_of_perm (I : Instance n) (σ : Equiv.Perm (Fin n)) (hc : IsCPS I.k σ)
    (hp : RespectsPrec I.prec σ) :
    IsPathIn I (win I.k σ) ∧ ∀ s (hs : s < n), (win I.k σ s).getLast? = some (σ ⟨s, hs⟩) := by
  have hlast : ∀ s (hs : s < n), (win I.k σ s).getLast? = some (σ ⟨s, hs⟩) := by
    intro s hs
    have hl := win_length I.k σ s hs
    apply getLast?_of _ (by omega)
    rw [List.getElem?_eq_getElem (by omega), win_getElem I.k σ s _ (by omega) ⟨s, hs⟩
      (by simp only; omega)]
  refine ⟨fun s hs => ⟨⟨⟨win_length I.k σ s hs, ?_, ?_⟩, ?_⟩, ?_⟩, hlast⟩
  · exact (List.nodup_ofFn.mpr σ.injective).sublist
      ((List.drop_sublist _ _).trans (List.take_sublist _ _))
  · intro m
    have hl := win_length I.k σ s hs
    have hm := m.2
    rw [List.get_eq_getElem, win_getElem I.k σ s m m.2 ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m,
      by omega⟩ rfl]
    have := hc ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m, by omega⟩
    have hidx : (((s + 1 - min (2 * I.k + 1) (s + 1) + (m : ℕ) : ℕ)) : ℤ)
        = (s : ℤ) + 1 - ((win I.k σ s).length : ℤ) + ((m : ℕ) : ℤ) := by
      omega
    rw [← hidx]; exact this
  · intro x y hxy hv
    have hl := win_length I.k σ s hs
    have hpr := hp x y hxy
    have cx := hc (σ.symm x)
    have cy := hc (σ.symm y)
    simp only [Equiv.apply_symm_apply] at cx cy
    rw [abs_le] at cx cy
    rcases hv with ⟨m₁, m₂, hlt, hy, hx⟩ | ⟨m, hy, hpos⟩ | ⟨m, hx, hpos⟩
    · have hm1 := m₁.2
      have hm2 := m₂.2
      rw [List.get_eq_getElem, win_getElem I.k σ s m₁ m₁.2
        ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m₁, by omega⟩ rfl] at hy
      rw [List.get_eq_getElem, win_getElem I.k σ s m₂ m₂.2
        ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m₂, by omega⟩ rfl] at hx
      rw [← hx, ← hy] at hpr
      simp only [Equiv.symm_apply_apply, Fin.lt_def] at hpr
      have : (m₁ : ℕ) < m₂ := hlt
      omega
    · have hm := m.2
      rw [List.get_eq_getElem, win_getElem I.k σ s m m.2
        ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m, by omega⟩ rfl] at hy
      rw [← hy] at hpr
      simp only [Equiv.symm_apply_apply, Fin.lt_def] at hpr
      omega
    · have hm := m.2
      rw [List.get_eq_getElem, win_getElem I.k σ s m m.2
        ⟨s + 1 - min (2 * I.k + 1) (s + 1) + m, by omega⟩ rfl] at hx
      rw [← hx] at hpr
      simp only [Equiv.symm_apply_apply, Fin.lt_def] at hpr
      omega
  · intro hs1
    unfold IsArc
    have hl := win_length I.k σ s hs
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

lemma perm_of_path (I : Instance n) (hprec : ∀ x y : Fin n, (x, y) ∈ I.prec → x ≠ y)
    (v : ℕ → List (Fin n)) (hv : IsPathIn I v) :
    ∃ σ : Equiv.Perm (Fin n), IsCPS I.k σ ∧ RespectsPrec I.prec σ ∧
      ∀ s (hs : s < n), (v s).getLast? = some (σ ⟨s, hs⟩) := by
  set f : Fin n → Fin n := fun p => pathSeq v p with hf
  have hlen : ∀ s, s < n → (v s).length = min (2 * I.k + 1) (s + 1) :=
    fun s hs => (hv s hs).1.1.1
  have key : ∀ s, s < n → ∀ m, m < min (2 * I.k + 1) (s + 1) → ∀ p : Fin n,
      (p : ℕ) = s + 1 - min (2 * I.k + 1) (s + 1) + m → (v s)[m]? = some (f p) := by
    intro s
    induction s with
    | zero =>
      intro hs m hm p hp
      have h0 := hlen 0 hs
      have hm0 : m = 0 := by omega
      have hp0 : p = ⟨0, hs⟩ := Fin.ext (by show (p : ℕ) = 0; omega)
      subst hm0 hp0
      have := getElem?_last (v 0) (⟨0, hs⟩ : Fin n) (by omega)
      rw [h0, show min (2 * I.k + 1) (0 + 1) - 1 = 0 by omega] at this
      exact this
    | succ s ih =>
      intro hs m hm p hp
      have h1 := hlen (s + 1) hs
      have h0 := hlen s (by omega)
      have harc := (hv s (by omega)).2 hs
      unfold IsArc at harc
      by_cases hmc : m < min (2 * I.k) (s + 1)
      · have e1 : (v (s + 1))[m]? = ((v (s + 1)).take (min (2 * I.k) (s + 1)))[m]? := by
          rw [List.getElem?_take_of_lt hmc]
        rw [e1, harc, List.getElem?_drop]
        exact ih (by omega) _ (by omega) p (by rw [hp, h0]; omega)
      · have hm' : m = (v (s + 1)).length - 1 := by omega
        have hp' : p = ⟨s + 1, hs⟩ := Fin.ext (by show (p : ℕ) = s + 1; omega)
        rw [hm', hp']
        exact getElem?_last _ (⟨s + 1, hs⟩ : Fin n) (by omega)
  have node_get : ∀ s (hs : s < n) m (hm : m < min (2 * I.k + 1) (s + 1)) (p : Fin n),
      (p : ℕ) = s + 1 - min (2 * I.k + 1) (s + 1) + m →
      (v s).get ⟨m, by rw [hlen s hs]; exact hm⟩ = f p := by
    intro s hs m hm p hp
    have h := key s hs m hm p hp
    rw [List.getElem?_eq_getElem (by rw [hlen s hs]; exact hm)] at h
    rw [List.get_eq_getElem]
    exact Option.some.inj h
  have adm : ∀ s (hs : s < n) m (hm : m < min (2 * I.k + 1) (s + 1)) (p : Fin n),
      (p : ℕ) = s + 1 - min (2 * I.k + 1) (s + 1) + m →
      |((f p : ℕ) : ℤ) - ((p : ℕ) : ℤ)| ≤ (I.k : ℤ) := by
    intro s hs m hm p hp
    have h := (hv s hs).1.1.2.2 ⟨m, by rw [hlen s hs]; exact hm⟩
    rw [node_get s hs m hm p hp] at h
    have hidx : ((p : ℕ) : ℤ) = (s : ℤ) + 1 - ((v s).length : ℤ) + (m : ℤ) := by
      rw [hlen s hs, hp]; omega
    rw [hidx]; exact h
  have adm1 : ∀ p : Fin n, |((f p : ℕ) : ℤ) - ((p : ℕ) : ℤ)| ≤ (I.k : ℤ) := by
    intro p
    exact adm p p.2 (min (2 * I.k + 1) (p + 1) - 1) (by omega) p (by omega)
  have finj : Function.Injective f := by
    have aux : ∀ p q : Fin n, (p : ℕ) < q → f p ≠ f q := by
      intro p q hpq hfe
      have ap := adm1 p
      have aq := adm1 q
      rw [hfe] at ap
      rw [abs_le] at ap aq
      have hnd := (hv q q.2).1.1.2.1
      have hql := hlen q q.2
      have g1 := node_get q q.2 (min (2 * I.k + 1) (q + 1) - 1 - ((q : ℕ) - p)) (by omega) p
        (by omega)
      have g2 := node_get q q.2 (min (2 * I.k + 1) (q + 1) - 1) (by omega) q (by omega)
      rw [hfe, ← g2] at g1
      have := (List.Nodup.get_inj_iff hnd).mp g1
      simp only [Fin.mk.injEq] at this
      omega
    intro p q hfe
    rcases lt_trichotomy (p : ℕ) q with h | h | h
    · exact absurd hfe (aux p q h)
    · exact Fin.ext h
    · exact absurd hfe.symm (aux q p h)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f ⟨finj, Finite.injective_iff_surjective.mp finj⟩
  have hσ : ∀ p, σ p = f p := fun p => rfl
  refine ⟨σ, ?_, ?_, ?_⟩
  · intro p; rw [hσ]; exact adm1 p
  · intro x y hxy
    have hne := hprec x y hxy
    set px := σ.symm x with hpx
    set py := σ.symm y with hpy
    have fx : f px = x := by rw [← hσ, hpx, Equiv.apply_symm_apply]
    have fy : f py = y := by rw [← hσ, hpy, Equiv.apply_symm_apply]
    rw [Fin.lt_def]
    by_contra hcon
    have hne' : (px : ℕ) ≠ py := fun h => hne (by rw [← fx, ← fy, Fin.ext h])
    have hlt : (py : ℕ) < px := by omega
    have ax := adm1 px
    rw [fx, abs_le] at ax
    by_cases hd : (px : ℕ) - py ≤ 2 * I.k
    · have hql := hlen px px.2
      have g1 := node_get px px.2 (min (2 * I.k + 1) (px + 1) - 1 - ((px : ℕ) - py)) (by omega)
        py (by omega)
      have g2 := node_get px px.2 (min (2 * I.k + 1) (px + 1) - 1) (by omega) px (by omega)
      rw [fy] at g1
      rw [fx] at g2
      refine (hv px px.2).1.2 x y hxy (Or.inl ⟨_, _, ?_, g1, g2⟩)
      show _ < _
      simp only [Fin.lt_def]
      omega
    · have hql := hlen py py.2
      have g1 := node_get py py.2 (min (2 * I.k + 1) (py + 1) - 1) (by omega) py (by omega)
      rw [fy] at g1
      refine (hv py py.2).1.2 x y hxy (Or.inr (Or.inl ⟨_, g1, ?_⟩))
      simp only [hql]
      omega
  · intro s hs
    apply getLast?_of _ (by rw [hlen s hs]; omega)
    rw [hσ]
    exact key s hs _ (by rw [hlen s hs]; omega) ⟨s, hs⟩ (by rw [hlen s hs]; simp only; omega)

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

end RunwayCPS.TotalDelay.P14301573

open RunwayCPS.TotalDelay in
theorem solution {n : ℕ} (I : Instance n)
    (hδ : ∀ a b : Fin n, 0 ≤ I.δ a b)
    (htri : ∀ a b c : Fin n, I.δ a c ≤ I.δ a b + I.δ b c)
    (hprec : ∀ x y : Fin n, (x, y) ∈ I.prec → x ≠ y) :
    ((∃ (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ), IsFeasible I σ t) ↔
        ∃ v : ℕ → List (Fin n), IsPathIn I v) ∧
    ∀ D : ℝ,
      IsLeast {x : ℝ | ∃ (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ),
          IsFeasible I σ t ∧ x = totalDelay t} D ↔
        IsLeast {x : ℝ | ∃ v : ℕ → List (Fin n), IsPathIn I v ∧ x = pathLength I v} D := by
  have plen : ∀ (v : ℕ → List (Fin n)) (σ : Fin n → Fin n),
      (∀ s (hs : s < n), (v s).getLast? = some (σ ⟨s, hs⟩)) → pathLength I v = P14301573.cost I σ := by
    intro v σ h
    unfold pathLength P14301573.cost
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [Finset.mem_Ico] at hs
    congr 1
    simp [nodeDelta, P14301573.e, h (s - 1) (by omega), h s hs.2, hs.2, show s - 1 < n by omega]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨σ, t, hc, hp, -, -⟩
    exact ⟨_, (P14301573.path_of_perm I σ hc hp).1⟩
  · rintro ⟨v, hv⟩
    obtain ⟨σ, hc, hp, -⟩ := P14301573.perm_of_path I hprec v hv
    obtain ⟨t, ht0, hsep, -⟩ := P14301573.greedy I hδ htri σ
    exact ⟨σ, t, hc, hp, ht0, hsep⟩
  · intro D
    apply P14301573.isLeast_iff_of
    · rintro x ⟨v, hv, rfl⟩
      obtain ⟨σ, hc, hp, hl⟩ := P14301573.perm_of_path I hprec v hv
      obtain ⟨t, ht0, hsep, htd⟩ := P14301573.greedy I hδ htri σ
      exact ⟨σ, t, ⟨hc, hp, ht0, hsep⟩, by rw [htd, plen v σ hl]⟩
    · rintro x ⟨σ, t, ⟨hc, hp, ht0, hsep⟩, rfl⟩
      obtain ⟨hv, hl⟩ := P14301573.path_of_perm I σ hc hp
      exact ⟨_, ⟨_, hv, rfl⟩, by rw [plen _ σ hl]; exact P14301573.lower I σ t ht0 hsep⟩
