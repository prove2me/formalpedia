-- Prove2me | solution 1 for SandsSauerWoodrow.two_coloured_digraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:18:57.781993+00:00
-- url     : https://prove2.me/submissions/04dbb4aa-31f0-4c2c-bded-88e6669269cb

import Mathlib
import Definitions.Def_SandsSauerWoodrow_MonoIndependent

namespace SSWInf

universe u

variable {V : Type u} (r : V → V → Prop)

/-- `n`-step paths. -/
def Pth : ℕ → V → V → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, r x z ∧ Pth n z y

theorem rtg_of_pth : ∀ n x y, Pth r n x y → Relation.ReflTransGen r x y
  | 0, x, y, h => by cases h; exact .refl
  | n + 1, x, y, ⟨z, hxz, hz⟩ => Relation.ReflTransGen.head hxz (rtg_of_pth n z y hz)

theorem pth_of_rtg {x y : V} (h : Relation.ReflTransGen r x y) : ∃ n, Pth r n x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hxz _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hxz, hn⟩

theorem wf_of_no_path
    (h : ¬ ∃ x : ℕ → V, Function.Injective x ∧ ∀ n, r (x n) (x (n + 1))) :
    WellFounded (fun b a => Relation.ReflTransGen r a b ∧ ¬ Relation.ReflTransGen r b a) := by
  classical
  haveI : IsStrictOrder V (fun b a => Relation.ReflTransGen r a b ∧
      ¬ Relation.ReflTransGen r b a) :=
    { irrefl := fun _ h => h.2 h.1
      trans := fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, fun h => h1.2 (h.trans h2.1)⟩ }
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => h ?_⟩
  let a : ℕ → V := f
  have ha : ∀ n, Relation.ReflTransGen r (a n) (a (n + 1)) ∧
      ¬ Relation.ReflTransGen r (a (n + 1)) (a n) := fun n =>
    f.map_rel_iff.2 (Nat.lt_succ_self n)
  have hmono : ∀ i j, i ≤ j → Relation.ReflTransGen r (a i) (a j) := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact .refl
    | succ j _ ih => exact ih.trans (ha j).1
  let m : V → ℕ := fun x => sInf {i | ¬ Relation.ReflTransGen r (a i) x}
  let Inv : V → Prop := fun x => Relation.ReflTransGen r x (a (m x))
  have hne : ∀ x j, Relation.ReflTransGen r x (a j) →
      {i | ¬ Relation.ReflTransGen r (a i) x}.Nonempty := by
    intro x j hx
    refine ⟨j + 1, fun h' => (ha j).2 (h'.trans hx)⟩
  have hm_lt : ∀ x i, i < m x → Relation.ReflTransGen r (a i) x := by
    intro x i hi
    by_contra hc
    exact absurd (Nat.sInf_le hc) (not_le.2 hi)
  have hm_mem : ∀ x j, Relation.ReflTransGen r x (a j) → ¬ Relation.ReflTransGen r (a (m x)) x :=
    fun x j hx => Nat.sInf_mem (hne x j hx)
  let d : V → ℕ := fun x => sInf {n | Pth r n x (a (m x))}
  have step : ∀ x, Inv x → ∃ y, r x y ∧ Inv y ∧ (m x < m y ∨ (m x = m y ∧ d y < d x)) := by
    intro x hx
    obtain ⟨n, hn⟩ := pth_of_rtg r hx
    have hd : Pth r (d x) x (a (m x)) :=
      Nat.sInf_mem (s := {n | Pth r n x (a (m x))}) ⟨n, hn⟩
    have hnot := hm_mem x _ hx
    rcases hdx : d x with _ | k
    · rw [hdx] at hd
      exact absurd (hd ▸ Relation.ReflTransGen.refl) hnot
    rw [hdx] at hd
    obtain ⟨y, hxy, hy⟩ := hd
    have hyt : Relation.ReflTransGen r y (a (m x)) := rtg_of_pth r _ _ _ hy
    have hmy : m x ≤ m y := by
      by_contra hc
      push Not at hc
      exact hm_mem y _ hyt ((hm_lt x _ hc).tail hxy)
    rcases lt_or_eq_of_le hmy with hlt | heq
    · exact ⟨y, hxy, hyt.trans (hmono _ _ hlt.le), Or.inl hlt⟩
    · have hInv : Inv y := by
        show Relation.ReflTransGen r y (a (m y))
        rw [← heq]; exact hyt
      refine ⟨y, hxy, hInv, Or.inr ⟨heq, ?_⟩⟩
      have : d y ≤ k := by
        apply Nat.sInf_le
        show Pth r k y (a (m y))
        rw [← heq]; exact hy
      omega
  let next : V → V := fun x => if hx : Inv x then Classical.choose (step x hx) else x
  have hnext : ∀ x, Inv x → r x (next x) ∧ Inv (next x) ∧
      (m x < m (next x) ∨ (m x = m (next x) ∧ d (next x) < d x)) := by
    intro x hx
    simp only [next, dif_pos hx]
    exact Classical.choose_spec (step x hx)
  let xs : ℕ → V := fun n => next^[n] (a 0)
  have hsucc : ∀ n, xs (n + 1) = next (xs n) := fun n => Function.iterate_succ_apply' next n _
  have hinv : ∀ n, Inv (xs n) := by
    intro n
    induction n with
    | zero => exact hmono 0 _ (Nat.zero_le _)
    | succ n ih => rw [hsucc]; exact (hnext _ ih).2.1
  let Φ : V → Lex (ℕ × ℕᵒᵈ) := fun x => toLex (m x, OrderDual.toDual (d x))
  have hΦ : StrictMono (Φ ∘ xs) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have := (hnext _ (hinv n)).2.2
    rw [← hsucc] at this
    simp only [Function.comp, Φ, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual]
    exact this
  refine ⟨xs, hΦ.injective.of_comp, fun n => ?_⟩
  rw [hsucc]
  exact (hnext _ (hinv n)).1

end SSWInf

namespace SSWInf

universe u

variable {V : Type u} (R B : V → V → Prop)

/-- Kernel of the union of two preorders under ascending chain conditions. -/
theorem kernel_two_preorders
    (hRr : ∀ x, R x x) (hRt : ∀ x y z, R x y → R y z → R x z)
    (hBr : ∀ x, B x x) (hBt : ∀ x y z, B x y → B y z → B x z)
    (wfR : WellFounded (fun b a => R a b ∧ ¬ R b a))
    (wfB : WellFounded (fun b a => B a b ∧ ¬ B b a)) :
    ∃ S : Set V, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y ∧ ¬ B x y) ∧
      ∀ x, x ∉ S → ∃ s ∈ S, R x s ∨ B x s := by
  classical
  let GB : V → V → Prop := fun b a => B a b ∧ ¬ B b a
  let Indep : Set V → Prop := fun S => ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ R x y ∧ ¬ B x y
  let RC : Set V → Prop := fun S => ∀ t ∈ S, ∀ v, R t v → ∃ s ∈ S, R v s ∨ B v s
  let F := {S : Set V // Indep S ∧ RC S}
  let le : F → F → Prop := fun S T => ∀ s ∈ S.1, s ∈ T.1 ∨ ∃ t ∈ T.1, GB t s
  have GBt : ∀ a b c, GB b a → GB c b → GB c a := fun a b c h1 h2 =>
    ⟨hBt _ _ _ h1.1 h2.1, fun h => h1.2 (hBt _ _ _ h2.1 h)⟩
  have le_trans : ∀ {S T U : F}, le S T → le T U → le S U := by
    intro S T U h1 h2 s hs
    rcases h1 s hs with h | ⟨t, ht, hst⟩
    · exact h2 s h
    · rcases h2 t ht with h | ⟨u, hu, htu⟩
      · exact Or.inr ⟨t, h, hst⟩
      · exact Or.inr ⟨u, hu, GBt _ _ _ hst htu⟩
  have bound : ∀ c : Set F, IsChain le c → ∃ ub : F, ∀ a ∈ c, le a ub := by
    intro c hc
    let Sinf : Set V := {v | ∃ S ∈ c, v ∈ S.1 ∧ ∀ U ∈ c, le S U → v ∈ U.1}
    -- every member of the chain lies below Sinf
    have hbelow : ∀ s, ∀ S ∈ c, s ∈ S.1 → s ∈ Sinf ∨ ∃ t ∈ Sinf, GB t s := by
      intro s
      induction s using wfB.induction with
      | h s ih =>
        intro S hS hs
        by_cases hin : s ∈ Sinf
        · exact Or.inl hin
        · have : ∃ U ∈ c, le S U ∧ s ∉ U.1 := by
            by_contra hcon
            push Not at hcon
            exact hin ⟨S, hS, hs, hcon⟩
          obtain ⟨U, hU, hSU, hsU⟩ := this
          rcases hSU s hs with h | ⟨u, hu, hsu⟩
          · exact absurd h hsU
          · rcases ih u hsu U hU hu with h | ⟨t, ht, hut⟩
            · exact Or.inr ⟨u, h, hsu⟩
            · exact Or.inr ⟨t, ht, GBt _ _ _ hsu hut⟩
    have hInd : Indep Sinf := by
      intro x ⟨Sx, hSx, hx, hxU⟩ y ⟨Sy, hSy, hy, hyU⟩ hxy
      by_cases hS : Sx = Sy
      · subst hS; exact Sx.2.1 x hx y hy hxy
      · rcases hc hSx hSy hS with h | h
        · exact Sy.2.1 x (hxU Sy hSy h) y hy hxy
        · exact Sx.2.1 x hx y (hyU Sx hSx h) hxy
    have hRC : RC Sinf := by
      intro t ⟨St, hSt, ht, _⟩ v htv
      obtain ⟨s, hs, hvs⟩ := St.2.2 t ht v htv
      by_cases hts : t = s
      · subst hts; exact ⟨t, ⟨St, hSt, ht, by assumption⟩, hvs⟩
      · rcases hvs with hvs | hvs
        · exact absurd (hRt _ _ _ htv hvs) (St.2.1 t ht s hs hts).1
        · rcases hbelow s St hSt hs with h | ⟨u, hu, hsu⟩
          · exact ⟨s, h, Or.inr hvs⟩
          · exact ⟨u, hu, Or.inr (hBt _ _ _ hvs hsu.1)⟩
    refine ⟨⟨Sinf, hInd, hRC⟩, fun S hS s hs => hbelow s S hS hs⟩
  obtain ⟨Sm, hmax⟩ := exists_maximal_of_chains_bounded bound le_trans
  refine ⟨Sm.1, Sm.2.1, ?_⟩
  by_contra hcon
  push Not at hcon
  let Se : Set V := {x | ¬ ∃ s ∈ Sm.1, R x s ∨ B x s}
  have hSe : Se.Nonempty := by
    obtain ⟨x, hx, hx'⟩ := hcon
    exact ⟨x, fun ⟨s, hs, h⟩ => h.elim (hx' s hs).1 (hx' s hs).2⟩
  obtain ⟨x, hxSe, hxmin⟩ := wfR.has_min Se hSe
  have hxabs : ∀ s ∈ Sm.1, ¬ R x s ∧ ¬ B x s := fun s hs =>
    ⟨fun h => hxSe ⟨s, hs, Or.inl h⟩, fun h => hxSe ⟨s, hs, Or.inr h⟩⟩
  have hxS : x ∉ Sm.1 := fun h => (hxabs x h).1 (hRr x)
  let T : Set V := {y | y ∈ Sm.1 ∧ ¬ B y x} ∪ {x}
  have hTind : Indep T := by
    have side : ∀ y ∈ Sm.1, ¬ B y x → ¬ R y x ∧ ¬ B y x := by
      intro y hy hyx
      refine ⟨fun h => ?_, hyx⟩
      obtain ⟨s, hs, h'⟩ := Sm.2.2 y hy x h
      exact hxSe ⟨s, hs, h'⟩
    rintro a (⟨ha, hax⟩ | ha) b (⟨hb, hbx⟩ | hb) hab
    · exact Sm.2.1 a ha b hb hab
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact side a ha hax
    · rw [Set.mem_singleton_iff] at ha; subst ha; exact hxabs b hb
    · rw [Set.mem_singleton_iff] at ha hb; exact absurd (ha.trans hb.symm) hab
  have hTrc : RC T := by
    have fin : ∀ v s, s ∈ Sm.1 → (R v s ∨ B v s) → ¬ (R v s) → ∃ s ∈ T, R v s ∨ B v s := by
      intro v s hs h hR
      have hB : B v s := h.resolve_left hR
      by_cases hsx : B s x
      · exact ⟨x, Or.inr rfl, Or.inr (hBt _ _ _ hB hsx)⟩
      · exact ⟨s, Or.inl ⟨hs, hsx⟩, Or.inr hB⟩
    rintro t (⟨ht, htx⟩ | ht) v htv
    · obtain ⟨s, hs, h⟩ := Sm.2.2 t ht v htv
      by_cases hsx : B s x
      · refine fin v s hs h (fun hR => ?_)
        have hts : t = s := by
          by_contra hne
          exact (Sm.2.1 t ht s hs hne).1 (hRt _ _ _ htv hR)
        exact htx (hts ▸ hsx)
      · exact ⟨s, Or.inl ⟨hs, hsx⟩, h⟩
    · rw [Set.mem_singleton_iff] at ht; subst ht
      by_cases hv : v ∈ Se
      · have : R v t := by
          by_contra h
          exact hxmin v hv ⟨htv, h⟩
        exact ⟨t, Or.inr rfl, Or.inl this⟩
      · simp only [Se, Set.mem_ofPred_eq, not_not] at hv
        obtain ⟨s, hs, h⟩ := hv
        by_cases hsx : B s t
        · exact fin v s hs h (fun hR => (hxabs s hs).1 (hRt _ _ _ htv hR))
        · exact ⟨s, Or.inl ⟨hs, hsx⟩, h⟩
  let T' : F := ⟨T, hTind, hTrc⟩
  have hle : le Sm T' := by
    intro s hs
    by_cases hsx : B s x
    · exact Or.inr ⟨x, Or.inr rfl, hsx, (hxabs s hs).2⟩
    · exact Or.inl (Or.inl ⟨hs, hsx⟩)
  rcases hmax T' hle x (Or.inr rfl) with h | ⟨t, ht, hxt⟩
  · exact hxS h
  · exact (hxabs t ht).2 hxt.1

end SSWInf

open OPG1808

universe u

namespace SSWInf

theorem mono_iff {V : Type u} (D : OPG1808.Digraph V) (color : OPG1808.ArcColoring V)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) (x y : V) :
    MonochromaticallyReaches D color x y ↔
      Relation.ReflTransGen (fun x y => D x y ∧ color x y = 0) x y ∨
      Relation.ReflTransGen (fun x y => D x y ∧ color x y = 1) x y := by
  constructor
  · rintro ⟨k, hk⟩
    rcases Relation.ReflTransGen.cases_head hk with h | ⟨w, ⟨hw, hwk⟩, _⟩
    · subst h; exact Or.inl .refl
    · rcases htwo _ _ hw with h0 | h1
      · rw [h0] at hwk; subst hwk; exact Or.inl hk
      · rw [h1] at hwk; subst hwk; exact Or.inr hk
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

end SSWInf

theorem solution {V : Type u} (D : OPG1808.Digraph V) (color : OPG1808.ArcColoring V)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1))
    (hno : SandsSauerWoodrow.NoMonoInfiniteOutwardPath D color) :
    ∃ S : Set V, SandsSauerWoodrow.MonoIndependent D color S ∧
      ∀ x : V, x ∉ S → ∃ s ∈ S, MonochromaticallyReaches D color x s := by
  have wf : ∀ k : Fin 3, WellFounded (fun b a =>
      Relation.ReflTransGen (fun x y => D x y ∧ color x y = k) a b ∧
      ¬ Relation.ReflTransGen (fun x y => D x y ∧ color x y = k) b a) := by
    intro k
    apply SSWInf.wf_of_no_path
    rintro ⟨x, hx, hpath⟩
    exact hno ⟨x, k, hx, hpath⟩
  obtain ⟨S, hS, habs⟩ := SSWInf.kernel_two_preorders
    (Relation.ReflTransGen (fun x y => D x y ∧ color x y = 0))
    (Relation.ReflTransGen (fun x y => D x y ∧ color x y = 1))
    (fun _ => .refl) (fun _ _ _ h1 h2 => h1.trans h2)
    (fun _ => .refl) (fun _ _ _ h1 h2 => h1.trans h2) (wf 0) (wf 1)
  refine ⟨S, fun x hx y hy hxy => ?_, fun x hx => ?_⟩
  · rw [SSWInf.mono_iff D color htwo, SSWInf.mono_iff D color htwo]
    have h1 := hS x hx y hy hxy
    have h2 := hS y hy x hx (Ne.symm hxy)
    exact ⟨fun h => h.elim h1.1 h1.2, fun h => h.elim h2.1 h2.2⟩
  · obtain ⟨s, hs, h⟩ := habs x hx
    exact ⟨s, hs, (SSWInf.mono_iff D color htwo x s).2 h⟩
