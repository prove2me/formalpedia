-- Prove2me | solution 1 for SeymourMFMC.Binary.noninitial_circuit
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T08:56:21.387628+00:00
-- url     : https://prove2.me/submissions/fcee68a4-7803-4b64-a6ae-948675e134f2

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Linarith
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_IsClutter
import Definitions.Def_SeymourMFMC_Binary_IsBinary
import Definitions.Def_SeymourMFMC_Binary_IsMengerian
import Definitions.Def_SeymourMFMC_Binary_IsCritical
import Definitions.Def_SeymourMFMC_Binary_IsCircuit
import Definitions.Def_SeymourMFMC_Binary_mb
import Definitions.Def_SeymourMFMC_Binary_Arrow
import Definitions.Def_SeymourMFMC_Binary_IsInitial
import Theorems.Thm_SeymourMFMC_Binary_arrow_asymm
import Theorems.Thm_SeymourMFMC_Binary_arrow_circuit
import Theorems.Thm_SeymourMFMC_Binary_circuit_card_ge_two
import Theorems.Thm_SeymourMFMC_Binary_parity_decomposition

namespace SeymourMFMC.Binary

private lemma arrow_irrefl {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (x : α) :
    ¬ Arrow L x x :=
  fun h => h.2.2.2 (Finset.mem_insert_self x _)

private lemma pair_inter_card_eq_one {α : Type*} [DecidableEq α] {u v : α} {B : Finset α}
    (hu : u ∈ B) (hv : v ∉ B) : ({u, v} ∩ B).card = 1 := by
  have heq : {u, v} ∩ B = {u} := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hwB⟩
      · rfl
      · exact (hv hwB).elim
    · rintro rfl
      exact ⟨Or.inl rfl, hu⟩
  rw [heq, Finset.card_singleton]

private lemma pair_circuit_mem_iff {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    {u v : α} (hC : IsCircuit L {u, v}) {B : Finset α} (hB : B ∈ blocker L) :
    u ∈ B ↔ v ∈ B := by
  rcases hC.2.1.2 B hB with ⟨k, hk⟩
  constructor
  · intro hu
    by_contra hv
    rw [pair_inter_card_eq_one hu hv] at hk
    omega
  · intro hv
    by_contra hu
    rw [Finset.pair_comm u v, pair_inter_card_eq_one hv hu] at hk
    omega

private lemma arrow_trans {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    {z y x : α} (hzy : Arrow L z y) (hyx : Arrow L y x) : Arrow L z x := by
  refine ⟨hzy.1, hyx.2.1, fun B hB hzB => hyx.2.2.1 B hB (hzy.2.2.1 B hB hzB), ?_⟩
  intro hx_pt
  rw [point, Finset.mem_insert, Finset.mem_filter] at hx_pt
  rcases hx_pt with rfl | ⟨_, hzx_circ⟩
  · exact arrow_asymm L hL hbin hM hcrit _ _ hzy.1 hzy.2.1 hzy hyx
  · have hxy : Arrow L x y := by
      refine ⟨hyx.2.1, hyx.1, ?_, ?_⟩
      · intro B hB hxB
        have hB_bl : B ∈ blocker L := (Finset.mem_filter.mp hB).1
        have hzB : z ∈ B := (pair_circuit_mem_iff L hzx_circ hB_bl).mpr hxB
        exact hzy.2.2.1 B hB hzB
      · intro hy_pt
        rw [point, Finset.mem_insert, Finset.mem_filter] at hy_pt
        rcases hy_pt with rfl | ⟨_, hxy_circ⟩
        · exact arrow_irrefl L _ hyx
        · apply hyx.2.2.2
          rw [point, Finset.mem_insert, Finset.mem_filter]
          exact Or.inr ⟨hyx.2.1, Finset.pair_comm x y ▸ hxy_circ⟩
    exact arrow_asymm L hL hbin hM hcrit y x hyx.1 hyx.2.1 hyx hxy

private def GoodCircuit {α : Type*} [DecidableEq α] (L : Finset (Finset α)) (x : α)
    (C : Finset α) : Prop :=
  IsCircuit L C ∧ x ∈ C ∧ (∀ y ∈ C.erase x, Arrow L y x) ∧
    ∀ B ∈ mb L, (B ∩ C.erase x).card ≤ 1

private lemma goodCircuit_card_ge_three {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) {x : α} {C : Finset α}
    (hC : GoodCircuit L x C) : 3 ≤ C.card := by
  have hge2 : 2 ≤ C.card := circuit_card_ge_two L hL hbin C hC.1
  have hcard_er : (C.erase x).card + 1 = C.card := Finset.card_erase_add_one hC.2.1
  obtain ⟨y, hy⟩ : (C.erase x).Nonempty := Finset.card_pos.mp (by omega)
  by_contra hlt
  have her_le : (C.erase x).card ≤ 1 := by omega
  have hC_eq : C = {y, x} := by
    ext w
    rw [← Finset.insert_erase hC.2.1, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton,
      Or.comm]
    refine or_congr_left ?_
    constructor
    · intro hw
      exact Finset.card_le_one.mp her_le w hw y hy
    · rintro rfl
      exact hy
  have hyx : Arrow L y x := hC.2.2.1 y hy
  apply hyx.2.2.2
  rw [point, Finset.mem_insert, Finset.mem_filter]
  exact Or.inr ⟨hyx.2.1, hC_eq ▸ hC.1⟩

private lemma exists_goodCircuit_of_not_isInitial {α : Type*} [DecidableEq α]
    (L : Finset (Finset α)) (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L)
    (hcrit : IsCritical L) {x : α} (hx : x ∈ ground L) (hni : ¬ IsInitial L x) :
    ∃ C : Finset α, GoodCircuit L x C := by
  unfold IsInitial at hni
  push Not at hni
  obtain ⟨y, _, hyx⟩ := hni hx
  obtain ⟨C, hC_circ, _, hxC, _, hC_arr, hC_tau⟩ :=
    arrow_circuit L hL hbin hM hcrit y x hyx
  refine ⟨C, hC_circ, hxC, hC_arr, ?_⟩
  intro B hB
  rw [mb, Finset.mem_filter] at hB
  have htau := hC_tau B hB.1
  have hsum := Finset.card_sdiff_add_card_inter B (C.erase x)
  omega

private lemma card_sdiff_inter_add_inter {α : Type*} [DecidableEq α]
    (X Y B : Finset α) :
    ((X \ Y) ∩ B).card + ((X ∩ Y) ∩ B).card = (X ∩ B).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    rw [← Finset.union_inter_distrib_right, Finset.sdiff_union_inter]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx1
    rw [Finset.mem_inter, Finset.mem_inter] at hx2
    exact hx1.1.2 hx2.1.2

private lemma card_symmDiff_inter {α : Type*} [DecidableEq α]
    (X Y B : Finset α) :
    (symmDiff X Y ∩ B).card + 2 * ((X ∩ Y) ∩ B).card = (X ∩ B).card + (Y ∩ B).card := by
  have h1 := card_sdiff_inter_add_inter X Y B
  have h2 := card_sdiff_inter_add_inter Y X B
  rw [Finset.inter_comm Y X] at h2
  have h3 : (symmDiff X Y ∩ B).card = ((X \ Y) ∩ B).card + ((Y \ X) ∩ B).card := by
    rw [Finset.symmDiff_def, Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_inter, Finset.mem_sdiff] at hx1 hx2
    exact hx1.1.2 hx2.1.1
  omega

private lemma step_goodCircuit {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    [DecidablePred (IsInitial L)]
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    {x y : α} {C Cy : Finset α}
    (hC : GoodCircuit L x C) (hy : y ∈ C.erase x) (hyni : ¬ IsInitial L y)
    (hCy : GoodCircuit L y Cy) (hCy_init : ∀ z ∈ Cy.erase y, IsInitial L z) :
    ∃ C' : Finset α, GoodCircuit L x C' ∧
      ((C'.erase x).filter (fun z => ¬ IsInitial L z)).card <
        ((C.erase x).filter (fun z => ¬ IsInitial L z)).card := by
  have hyx : Arrow L y x := hC.2.2.1 y hy
  have hyC : y ∈ C := Finset.mem_of_mem_erase hy
  have hyCy : y ∈ Cy := hCy.2.1
  have hx_not_Cy : x ∉ Cy := by
    intro hxCy
    have hxy_ne : x ≠ y := fun h => arrow_irrefl L y (h ▸ hyx)
    have hxy : Arrow L x y := hCy.2.2.1 x (Finset.mem_erase.mpr ⟨hxy_ne, hxCy⟩)
    exact arrow_asymm L hL hbin hM hcrit y x hyx.1 hyx.2.1 hyx hxy
  let Z := symmDiff C Cy
  have hxZ : x ∈ Z := Finset.mem_symmDiff.mpr (Or.inl ⟨hC.2.1, hx_not_Cy⟩)
  have hy_not_Z : y ∉ Z := by
    rw [Finset.mem_symmDiff]
    rintro (⟨_, hyCy'⟩ | ⟨_, hyC'⟩)
    · exact hyCy' hyCy
    · exact hyC' hyC
  have hZ_sub : ∀ z ∈ Z.erase x, z ∈ C.erase x ∨ z ∈ Cy.erase y := by
    intro z hz
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    have hzZ : z ∈ Z := (Finset.mem_erase.mp hz).2
    have hzy : z ≠ y := fun h => hy_not_Z (h ▸ hzZ)
    rw [Finset.mem_symmDiff] at hzZ
    rcases hzZ with ⟨hzC, _⟩ | ⟨hzCy, _⟩
    · exact Or.inl (Finset.mem_erase.mpr ⟨hzx, hzC⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hzy, hzCy⟩)
  have hZ_arr : ∀ z ∈ Z.erase x, Arrow L z x := by
    intro z hz
    rcases hZ_sub z hz with hzC | hzCy
    · exact hC.2.2.1 z hzC
    · exact arrow_trans L hL hbin hM hcrit (hCy.2.2.1 z hzCy) hyx
  have hZ_mb : ∀ B ∈ mb L, (B ∩ Z.erase x).card ≤ 1 := by
    intro B hB
    by_cases hyB : y ∈ B
    · have hsub : B ∩ Z.erase x ⊆ B ∩ Cy.erase y := by
        intro z hz
        rw [Finset.mem_inter] at hz ⊢
        rcases hz with ⟨hzB, hz_er⟩
        have hzx : z ≠ x := (Finset.mem_erase.mp hz_er).1
        have hzZ : z ∈ Z := (Finset.mem_erase.mp hz_er).2
        have hzy : z ≠ y := fun h => hy_not_Z (h ▸ hzZ)
        have hz_not_C : z ∉ C := by
          intro hzC
          have hz_inter : z ∈ B ∩ C.erase x :=
            Finset.mem_inter.mpr ⟨hzB, Finset.mem_erase.mpr ⟨hzx, hzC⟩⟩
          have hy_inter : y ∈ B ∩ C.erase x := Finset.mem_inter.mpr ⟨hyB, hy⟩
          exact hzy (Finset.card_le_one.mp (hC.2.2.2 B hB) z hz_inter y hy_inter)
        rw [Finset.mem_symmDiff] at hzZ
        rcases hzZ with ⟨hzC, _⟩ | ⟨hzCy, _⟩
        · exact (hz_not_C hzC).elim
        · exact ⟨hzB, Finset.mem_erase.mpr ⟨hzy, hzCy⟩⟩
      exact (Finset.card_le_card hsub).trans (hCy.2.2.2 B hB)
    · have hsub : B ∩ Z.erase x ⊆ B ∩ C.erase x := by
        intro z hz
        rw [Finset.mem_inter] at hz ⊢
        rcases hz with ⟨hzB, hz_er⟩
        rcases hZ_sub z hz_er with hzC | hzCy
        · exact ⟨hzB, hzC⟩
        · exact (hyB ((hCy.2.2.1 z hzCy).2.2.1 B hB hzB)).elim
      exact (Finset.card_le_card hsub).trans (hC.2.2.2 B hB)
  have hZG : Z ⊆ ground L := by
    intro z hz
    rw [Finset.mem_symmDiff] at hz
    rcases hz with ⟨hzC, _⟩ | ⟨hzCy, _⟩
    · exact hC.1.2.1.1 hzC
    · exact hCy.1.2.1.1 hzCy
  have hZeven : ∀ B ∈ blocker L, Even (Z ∩ B).card := by
    intro B hB
    dsimp only [Z]
    have hsum := card_symmDiff_inter C Cy B
    rcases hC.1.2.1.2 B hB with ⟨k, hk⟩
    rcases hCy.1.2.1.2 B hB with ⟨m, hm⟩
    refine ⟨k + m - ((C ∩ Cy) ∩ B).card, ?_⟩
    omega
  obtain ⟨Cs, hCs_circ, _, hCs_sup⟩ := (parity_decomposition L hL hbin Z hZG).1 hZeven
  have hx_sup : x ∈ Cs.sup id := hCs_sup.symm ▸ hxZ
  rw [Finset.mem_sup] at hx_sup
  rcases hx_sup with ⟨C', hC'Cs, hxC'⟩
  have hC'Z : C' ⊆ Z := hCs_sup ▸ Finset.le_sup (f := id) hC'Cs
  have hC'_er_Z : C'.erase x ⊆ Z.erase x := Finset.erase_subset_erase x hC'Z
  refine ⟨C', ⟨hCs_circ C' hC'Cs, hxC', fun z hz => hZ_arr z (hC'_er_Z hz), ?_⟩, ?_⟩
  · intro B hB
    have hsub : B ∩ C'.erase x ⊆ B ∩ Z.erase x :=
      Finset.inter_subset_inter_left hC'_er_Z
    exact (Finset.card_le_card hsub).trans (hZ_mb B hB)
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨y, Finset.mem_filter.mpr ⟨hy, hyni⟩, ?_⟩
      rw [Finset.mem_filter]
      rintro ⟨hyC', _⟩
      exact hy_not_Z (hC'Z (Finset.mem_of_mem_erase hyC'))
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      rcases hz with ⟨hzC', hzni⟩
      rcases hZ_sub z (hC'_er_Z hzC') with hzC | hzCy
      · exact ⟨hzC, hzni⟩
      · exact (hzni (hCy_init z hzCy)).elim

private lemma elim_bad_goodCircuit {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    [DecidablePred (IsInitial L)]
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    {x : α}
    (ih_anc : ∀ y ∈ ground L, ¬ IsInitial L y → Arrow L y x →
      ∃ Cy : Finset α, GoodCircuit L y Cy ∧ ∀ z ∈ Cy.erase y, IsInitial L z) :
    ∀ (m : ℕ) (C : Finset α),
      ((C.erase x).filter (fun z => ¬ IsInitial L z)).card = m →
      GoodCircuit L x C →
      ∃ C' : Finset α, GoodCircuit L x C' ∧ ∀ z ∈ C'.erase x, IsInitial L z := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ihm =>
    intro C hcard hC
    rcases ((C.erase x).filter (fun z => ¬ IsInitial L z)).eq_empty_or_nonempty with hemp | hne
    · refine ⟨C, hC, fun z hz => ?_⟩
      by_contra hzni
      have hmem : z ∈ (C.erase x).filter (fun z => ¬ IsInitial L z) :=
        Finset.mem_filter.mpr ⟨hz, hzni⟩
      rw [hemp] at hmem
      exact Finset.notMem_empty z hmem
    · rcases hne with ⟨y, hy_filt⟩
      rw [Finset.mem_filter] at hy_filt
      rcases hy_filt with ⟨hy, hyni⟩
      have hyx : Arrow L y x := hC.2.2.1 y hy
      obtain ⟨Cy, hCy, hCy_init⟩ := ih_anc y hyx.1 hyni hyx
      obtain ⟨C₁, hC₁, hlt⟩ :=
        step_goodCircuit L hL hbin hM hcrit hC hy hyni hCy hCy_init
      exact ihm _ (hcard ▸ hlt) C₁ rfl hC₁

/-- Seymour 1977, (4.5), p. 207: if `L` is a critical Mengerian binary clutter and `x ∈ E(L)` is
not initial, then there is a circuit `C` of `L` such that (i) `x ∈ C`, (ii) all other members of
`C` are initial, (iii) `y → x` for every `y ∈ C − {x}`, (iv) `|C| ≥ 3`, and
(v) `|B ∩ (C − {x})| ≤ 1` for every `B ∈ mb(L)`. -/
theorem noninitial_circuit {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : IsClutter L) (hbin : IsBinary L) (hM : IsMengerian L) (hcrit : IsCritical L)
    (x : α) (hx : x ∈ ground L) (hni : ¬ IsInitial L x) :
    ∃ C : Finset α, IsCircuit L C ∧ x ∈ C ∧ (∀ y ∈ C.erase x, IsInitial L y) ∧
      (∀ y ∈ C.erase x, Arrow L y x) ∧ 3 ≤ C.card ∧
      ∀ B ∈ mb L, (B ∩ C.erase x).card ≤ 1 := by
  classical
  let anc (u : α) : Finset α := (ground L).filter (fun z => Arrow L z u)
  have hmain : ∀ (k : ℕ) (u : α), (anc u).card = k → u ∈ ground L → ¬ IsInitial L u →
      ∃ C : Finset α, GoodCircuit L u C ∧ ∀ y ∈ C.erase u, IsInitial L y := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro u hcard hu huni
      obtain ⟨C₀, hC₀⟩ := exists_goodCircuit_of_not_isInitial L hL hbin hM hcrit hu huni
      refine elim_bad_goodCircuit L hL hbin hM hcrit ?_ _ C₀ rfl hC₀
      intro y hyG hyni hyu
      have hss : anc y ⊂ anc u := by
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨y, Finset.mem_filter.mpr ⟨hyG, hyu⟩, ?_⟩
          rw [Finset.mem_filter]
          rintro ⟨_, hyy⟩
          exact arrow_irrefl L y hyy
        · intro z hz
          rw [Finset.mem_filter] at hz ⊢
          exact ⟨hz.1, arrow_trans L hL hbin hM hcrit hz.2 hyu⟩
      have hlt : (anc y).card < k := hcard ▸ Finset.card_lt_card hss
      exact ih _ hlt y rfl hyG hyni
  obtain ⟨C, hC, hC_init⟩ := hmain (anc x).card x rfl hx hni
  exact ⟨C, hC.1, hC.2.1, hC_init, hC.2.2.1, goodCircuit_card_ge_three L hL hbin hC, hC.2.2.2⟩

end SeymourMFMC.Binary

theorem solution {α : Type*} [DecidableEq α] (L : Finset (Finset α))
    (hL : SeymourMFMC.Binary.IsClutter L) (hbin : SeymourMFMC.Binary.IsBinary L)
    (hM : SeymourMFMC.Binary.IsMengerian L) (hcrit : SeymourMFMC.Binary.IsCritical L)
    (x : α) (hx : x ∈ SeymourMFMC.Binary.ground L) (hni : ¬ SeymourMFMC.Binary.IsInitial L x) :
    ∃ C : Finset α, SeymourMFMC.Binary.IsCircuit L C ∧ x ∈ C ∧
      (∀ y ∈ C.erase x, SeymourMFMC.Binary.IsInitial L y) ∧
      (∀ y ∈ C.erase x, SeymourMFMC.Binary.Arrow L y x) ∧ 3 ≤ C.card ∧
      ∀ B ∈ SeymourMFMC.Binary.mb L, (B ∩ C.erase x).card ≤ 1 :=
  SeymourMFMC.Binary.noninitial_circuit L hL hbin hM hcrit x hx hni
