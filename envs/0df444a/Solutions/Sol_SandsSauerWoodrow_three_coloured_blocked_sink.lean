-- Prove2me | solution 1 for SandsSauerWoodrow.three_coloured_blocked_sink
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T02:11:51.760609+00:00
-- url     : https://prove2.me/submissions/e5c2c982-6b1a-4cc9-ac22-b42f4f2eb098

import Mathlib
import Definitions.Def_opg1808_colored_tournaments

open OPG1808

universe u

namespace SSWAux


variable {V : Type u} (D : OPG1808.Digraph V) (color : OPG1808.ArcColoring V)

theorem fin3_two : ∀ a b d : Fin 3, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → (d = 0 ∨ d = 1) →
    b ≠ a → d = a ∨ d = b := by decide

theorem finset_sink' [DecidableEq V] (P : Set V)
    (htour : ∀ u v, u ∈ P → v ∈ P → u ≠ v → D u v ∨ D v u)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∀ (S : Finset V), (↑S : Set V) ⊆ P → S.Nonempty →
      ∃ v ∈ S, ∀ x ∈ S, x ≠ v → MonochromaticallyReaches D color x v := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hSP hne
  by_contra hcon
  push Not at hcon
  -- each x ∈ S has a sink of S.erase x
  have key : ∀ x ∈ S, ∃ y, y ∈ S ∧ y ≠ x ∧
      (∀ z ∈ S, z ≠ x → z ≠ y → MonochromaticallyReaches D color z y) ∧
      ¬ MonochromaticallyReaches D color x y ∧ D y x := by
    intro x hx
    have hne' : (S.erase x).Nonempty := by
      obtain ⟨w, hw, hw', _⟩ := hcon x hx
      exact ⟨w, Finset.mem_erase.2 ⟨hw', hw⟩⟩
    obtain ⟨y, hy, hyr⟩ := ih (S.erase x) (Finset.erase_ssubset hx)
      (fun z hz => hSP (Finset.mem_of_mem_erase hz)) hne'
    obtain ⟨hyx, hyS⟩ := Finset.mem_erase.1 hy
    have hr : ∀ z ∈ S, z ≠ x → z ≠ y → MonochromaticallyReaches D color z y :=
      fun z hz hzx hzy => hyr z (Finset.mem_erase.2 ⟨hzx, hz⟩) hzy
    have hnx : ¬ MonochromaticallyReaches D color x y := by
      intro h
      obtain ⟨w, hw, hw', hwr⟩ := hcon y hyS
      apply hwr
      by_cases hwx : w = x
      · subst hwx; exact h
      · exact hr w hw hwx hw'
    refine ⟨y, hyS, hyx, hr, hnx, ?_⟩
    rcases htour x y (hSP hx) (hSP hyS) (Ne.symm hyx) with h | h
    · exfalso; apply hnx
      exact ⟨color x y, Relation.ReflTransGen.single ⟨h, rfl⟩⟩
    · exact h
  classical
  let s : V → V := fun x => if hx : x ∈ S then Classical.choose (key x hx) else x
  have hs : ∀ x ∈ S, s x ∈ S ∧ s x ≠ x ∧
      (∀ z ∈ S, z ≠ x → z ≠ s x → MonochromaticallyReaches D color z (s x)) ∧
      ¬ MonochromaticallyReaches D color x (s x) ∧ D (s x) x := by
    intro x hx
    have := Classical.choose_spec (key x hx)
    simp only [s, dif_pos hx]
    exact this
  obtain ⟨x0, hx0⟩ := hne
  let xs : ℕ → V := fun n => s^[n] x0
  have hsucc : ∀ n, xs (n + 1) = s (xs n) := fun n =>
    Function.iterate_succ_apply' s n x0
  have hmem : ∀ n, xs n ∈ S := by
    intro n
    induction n with
    | zero => exact hx0
    | succ n ihn => rw [hsucc]; exact (hs _ ihn).1
  have hS : ∀ n, xs (n + 1) ≠ xs n ∧
      (∀ z ∈ S, z ≠ xs n → z ≠ xs (n + 1) → MonochromaticallyReaches D color z (xs (n + 1))) ∧
      ¬ MonochromaticallyReaches D color (xs n) (xs (n + 1)) ∧ D (xs (n + 1)) (xs n) := by
    intro n
    rw [hsucc]
    exact (hs _ (hmem n)).2
  set c := color (xs 1) (xs 0) with hc
  -- all back arcs have colour c
  have hcol : ∀ n, color (xs (n + 1)) (xs n) = c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ihn =>
      by_contra hne
      have h1 := hS n
      have h2 := hS (n + 1)
      have hD2 : D (xs (n + 2)) (xs (n + 1)) := h2.2.2.2
      have hD1 : D (xs (n + 1)) (xs n) := h1.2.2.2
      by_cases heq : xs n = xs (n + 2)
      · apply h1.2.2.1
        rw [heq]
        exact ⟨_, Relation.ReflTransGen.single ⟨hD2, rfl⟩⟩
      · obtain ⟨d, hd⟩ := h2.2.1 (xs n) (hmem n) (fun h => h1.1 h.symm) heq
        rcases Relation.ReflTransGen.cases_head hd with h | ⟨w, ⟨hw, hwd⟩, _⟩
        · exact heq h
        have hd01 := htwo _ _ hw
        rw [hwd] at hd01
        have hc01 := htwo _ _ hD1
        rw [ihn] at hc01
        rcases fin3_two c _ d hc01 (htwo _ _ hD2) hd01 hne with hdc | hdc
        · -- x_{n+1} → x_n ⇝ x_{n+2} in colour c
          apply h2.2.2.1
          refine ⟨c, Relation.ReflTransGen.head ⟨hD1, ihn⟩ ?_⟩
          rw [← hdc]; exact hd
        · -- x_n ⇝ x_{n+2} → x_{n+1} in colour d
          apply h1.2.2.1
          exact ⟨d, Relation.ReflTransGen.tail hd ⟨hD2, hdc.symm⟩⟩
  have hback : ∀ m n, m ≤ n →
      Relation.ReflTransGen (fun x y => D x y ∧ color x y = c) (xs n) (xs m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Relation.ReflTransGen.refl
    | succ n _ ihn => exact Relation.ReflTransGen.head ⟨(hS n).2.2.2, hcol n⟩ ihn
  obtain ⟨a, b, hab, habeq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (⟨xs n, hmem n⟩ : S))
  simp only [Subtype.mk.injEq] at habeq
  rcases lt_or_gt_of_ne hab with h | h
  · apply (hS a).2.2.1
    refine ⟨c, ?_⟩
    rw [habeq]; exact hback (a + 1) b h
  · apply (hS b).2.2.1
    refine ⟨c, ?_⟩
    rw [← habeq]; exact hback (b + 1) a h

theorem finset_sink [DecidableEq V] (htournament : IsTournament D)
    (htwo : ∀ u v, D u v → (color u v = 0 ∨ color u v = 1)) :
    ∀ (S : Finset V), S.Nonempty →
      ∃ v ∈ S, ∀ x ∈ S, x ≠ v → MonochromaticallyReaches D color x v :=
  fun S hS => finset_sink' D color Set.univ (fun _ _ _ _ h => (htournament.2 h).1) htwo S
    (Set.subset_univ _) hS

end SSWAux


universe v

namespace SSWBlock

variable {V : Type u} {ι : Type v} (D : OPG1808.Digraph V) (color : OPG1808.ArcColoring V)

theorem fin3_shift : ∀ c k : Fin 3, (c = 1 ∨ c = 2) → (if c = 2 then (1 : Fin 3) else 0) = k →
    c = k + 1 := by decide

theorem terminal_exists [Fintype V] (R : V → V → Prop) (x : V) :
    ∃ t, Relation.ReflTransGen R x t ∧
      ∀ w, Relation.ReflTransGen R t w → Relation.ReflTransGen R w t := by
  classical
  let Rs : V → Finset V := fun w => Finset.univ.filter (fun z => Relation.ReflTransGen R w z)
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun z => Relation.ReflTransGen R x z)) (fun w => (Rs w).card)
    ⟨x, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact .refl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht hmin
  refine ⟨t, ht, fun w hw => ?_⟩
  have hsub : Rs w ⊆ Rs t := by
    intro z hz
    simp only [Rs, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact hw.trans hz
  have heq : Rs w = Rs t := Finset.eq_of_subset_of_card_le hsub (hmin w (ht.trans hw))
  have : t ∈ Rs w := by
    rw [heq]; simp only [Rs, Finset.mem_filter, Finset.mem_univ, true_and]; exact .refl
  simpa [Rs] using this

theorem blocked [Fintype V] [Nonempty V]
    (htournament : IsTournament D)
    (b : V → ι)
    (hred : ∀ u v, D u v → b u ≠ b v → color u v = 0)
    (hbg : ∀ u v, D u v → b u = b v → (color u v = 1 ∨ color u v = 2)) :
    ∃ v : V, ∀ x : V, x ≠ v → MonochromaticallyReaches D color x v := by
  classical
  let Rr := Relation.ReflTransGen (fun x y => D x y ∧ color x y = 0)
  have hredb : ∀ u v, D u v → color u v = 0 → b u ≠ b v := by
    intro u v h h0 hb
    rcases hbg u v h hb with h1 | h1 <;> rw [h0] at h1 <;> exact absurd h1 (by decide)
  have arc : ∀ u v, b u ≠ b v → (D u v ∧ color u v = 0) ∨ (D v u ∧ color v u = 0) := by
    intro u v hb
    have hne : u ≠ v := fun h => hb (h ▸ rfl)
    rcases (htournament.2 hne).1 with h | h
    · exact Or.inl ⟨h, hred u v h hb⟩
    · exact Or.inr ⟨h, hred v u h (Ne.symm hb)⟩
  let Term : V → Prop := fun t => ∀ w, Rr t w → Rr w t
  obtain ⟨x0⟩ := ‹Nonempty V›
  by_cases hA : ∃ v z, Term v ∧ D v z ∧ color v z = 0
  · obtain ⟨v, z, hv, hvz, hvz0⟩ := hA
    have hzv : Rr z v := hv z (Relation.ReflTransGen.single ⟨hvz, hvz0⟩)
    refine ⟨v, fun x _ => ⟨0, ?_⟩⟩
    obtain ⟨t, hxt, ht⟩ := terminal_exists (fun x y => D x y ∧ color x y = 0) x
    refine hxt.trans ?_
    by_cases hbt : b t = b v
    · have hbz : b t ≠ b z := by rw [hbt]; exact hredb v z hvz hvz0
      rcases arc t z hbz with h | h
      · exact (Relation.ReflTransGen.single (r := fun x y => D x y ∧ color x y = 0) h).trans hzv
      · exact hv t ((Relation.ReflTransGen.single ⟨hvz, hvz0⟩).trans
          (Relation.ReflTransGen.single (r := fun x y => D x y ∧ color x y = 0) h))
    · rcases arc t v hbt with h | h
      · exact Relation.ReflTransGen.single h
      · exact hv t (Relation.ReflTransGen.single (r := fun x y => D x y ∧ color x y = 0) h)
  · push Not at hA
    -- all terminal vertices have no red out-arcs, hence lie in one block
    obtain ⟨t0, -, ht0⟩ := terminal_exists (fun x y => D x y ∧ color x y = 0) x0
    have hK : ∀ t, Term t → b t = b t0 := by
      intro t ht
      by_contra hb
      rcases arc t t0 hb with h | h
      · exact hA t t0 ht h.1 h.2
      · exact hA t0 t ht0 h.1 h.2
    let K : Finset V := Finset.univ.filter Term
    have hKne : K.Nonempty := ⟨t0, by simp [K]; exact ht0⟩
    let D' : OPG1808.Digraph V := fun x y => D x y ∧ Term x ∧ Term y
    let color' : OPG1808.ArcColoring V := fun x y => if color x y = 2 then 1 else 0
    have htour' : ∀ u v, u ∈ (↑K : Set V) → v ∈ (↑K : Set V) → u ≠ v → D' u v ∨ D' v u := by
      intro u v hu hv huv
      simp only [K, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
      rcases (htournament.2 huv).1 with h | h
      · exact Or.inl ⟨h, hu, hv⟩
      · exact Or.inr ⟨h, hv, hu⟩
    have htwo' : ∀ u v, D' u v → (color' u v = 0 ∨ color' u v = 1) := by
      intro u v _
      simp only [color']
      split_ifs <;> simp
    obtain ⟨v, hvK, hv⟩ := SSWAux.finset_sink' D' color' (↑K) htour' htwo' K subset_rfl hKne
    have hvT : Term v := by simpa [K] using hvK
    have hvb : b v = b t0 := hK v hvT
    -- every vertex outside the block red-reaches every terminal vertex
    have hout : ∀ x, b x ≠ b t0 → ∀ k, Term k → D x k ∧ color x k = 0 := by
      intro x hx k hk
      rcases arc x k (by rw [hK k hk]; exact hx) with h | h
      · exact h
      · exact absurd h.2 (hA k x hk h.1)
    refine ⟨v, fun x hxv => ?_⟩
    by_cases hxb : b x = b t0
    · by_cases hxT : Term x
      · -- inside K: use the blue/green sink
        obtain ⟨k, hk⟩ := hv x (by simp [K]; exact hxT) hxv
        refine ⟨k + 1, Relation.ReflTransGen.mono ?_ _ _ hk⟩
        rintro y z ⟨⟨hyz, hy, hz⟩, hc⟩
        refine ⟨hyz, fin3_shift _ _ (hbg y z hyz ?_) hc⟩
        rw [hK y hy, hK z hz]
      · -- not terminal: a nontrivial red path leaves the block
        obtain ⟨t, hxt, ht⟩ := terminal_exists (fun x y => D x y ∧ color x y = 0) x
        rcases Relation.ReflTransGen.cases_head hxt with h | ⟨z, hxz, -⟩
        · exact absurd (h ▸ ht) hxT
        · have hzb : b z ≠ b t0 := by rw [← hxb]; exact Ne.symm (hredb x z hxz.1 hxz.2)
          exact ⟨0, Relation.ReflTransGen.head hxz
            (Relation.ReflTransGen.single (r := fun x y => D x y ∧ color x y = 0) (hout z hzb v hvT))⟩
    · exact ⟨0, Relation.ReflTransGen.single (r := fun x y => D x y ∧ color x y = 0) (hout x hxb v hvT)⟩

end SSWBlock
theorem solution {V : Type u} {ι : Type v} [Fintype V] [Nonempty V]
    (D : OPG1808.Digraph V) (color : OPG1808.ArcColoring V) (htournament : IsTournament D)
    (b : V → ι)
    (hred : ∀ u v, D u v → b u ≠ b v → color u v = 0)
    (hbg : ∀ u v, D u v → b u = b v → (color u v = 1 ∨ color u v = 2)) :
    ∃ v : V, ∀ x : V, x ≠ v → MonochromaticallyReaches D color x v :=
  SSWBlock.blocked D color htournament b hred hbg
