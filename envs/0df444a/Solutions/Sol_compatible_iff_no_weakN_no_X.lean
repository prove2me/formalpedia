-- Prove2me | solution 1 for compatible_iff_no_weakN_no_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:10:41.462739+00:00
-- url     : https://prove2.me/submissions/af6aed1f-5438-4b8f-b9ae-1cbc52474dcf

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
import Theorems.Thm_not_compatible_if_weakN
import Theorems.Thm_not_compatible_if_X
attribute [local simp] perp_iff
section
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
private lemma veryWeakN_aux (x y : P) (hxy : x < y)
    (hfall : ∀ z : P, ¬ (incompSet x ∪ incompSet y ⊆ incompSet z)) :
    ∃ a d : P, IsVeryWeakN a x y d := by
  -- x⊥ ⊄ y⊥: otherwise z = y witnesses compatibility
  have hx_not_sub : ¬ (incompSet x ⊆ incompSet y) := fun h =>
    hfall y (Set.union_subset h (Set.Subset.refl _))
  -- y⊥ ⊄ x⊥: otherwise z = x witnesses compatibility
  have hy_not_sub : ¬ (incompSet y ⊆ incompSet x) := fun h =>
    hfall x (Set.union_subset (Set.Subset.refl _) h)
  -- pick a ∈ x⊥ \ y⊥ and d ∈ y⊥ \ x⊥
  obtain ⟨a, ha_x, ha_y⟩ := Set.not_subset.mp hx_not_sub
  obtain ⟨d, hd_y, hd_x⟩ := Set.not_subset.mp hy_not_sub
  -- unfold incompSet membership
  simp only [incompSet, Set.mem_setOf_eq] at ha_x ha_y hd_y hd_x
  -- ha_x : x ⊥ a,  ha_y : ¬ y ⊥ a  →  comparable, so y ≤ a ∨ a ≤ y
  -- hd_y : y ⊥ d,  hd_x : ¬ x ⊥ d  →  comparable, so x ≤ d ∨ d ≤ x
  simp only [perp_iff, not_and_or, not_not] at ha_y hd_x
  -- a < y: y ≤ a gives x ≤ a contradicting ha_x; a = y gives x ⊥ y contradicting hxy
  have hay : a < y := by
    rcases ha_y with hya | hay
    · exact absurd (hxy.le.trans hya) ha_x.1
    · rcases hay.lt_or_eq with h | h
      · exact h
      · exact absurd hxy.le (h ▸ ha_x).1
  -- x < d: d ≤ x gives d ≤ y contradicting hd_y; d = x gives y ⊥ x contradicting hxy
  have hxd : x < d := by
    rcases hd_x with hxd | hdx
    · rcases hxd.lt_or_eq with h | h
      · exact h
      · exact absurd hxy.le (h.symm ▸ hd_y).2
    · exact absurd (hdx.trans hxy.le) hd_y.2
  -- witnesses: IsVeryWeakN a x y d
  exact ⟨a, d, hay, hxy, hxd, ⟨ha_x.2, ha_x.1⟩, hd_y⟩
private lemma chain_claim (x y : P)
    (hfall : ∀ z : P, ¬ (incompSet x ∪ incompSet y ⊆ incompSet z))
    {z : P} (hxz : x < z) (hzy : z < y) :
    (∃ w : P, (x ⊥ w) ∧ w < z) ∨ (∃ w : P, z < w ∧ (y ⊥ w)) := by
  -- z does not witness compatibility, so some u ∈ incompSet x ∪ incompSet y is comparable to z
  obtain ⟨u, hu_in, hu_ninc⟩ := Set.not_subset.mp (hfall z)
  simp only [incompSet, Set.mem_setOf_eq] at hu_ninc
  simp only [perp_iff, not_and_or, not_not] at hu_ninc
  -- hu_ninc : z ≤ u ∨ u ≤ z
  rw [Set.mem_union] at hu_in
  rcases hu_in with hxu | hyu
  · -- u ∈ incompSet x, i.e., x ⊥ u
    simp only [incompSet, Set.mem_setOf_eq] at hxu
    rcases hu_ninc with hzu | huz
    · -- z ≤ u: then x < z ≤ u contradicts x ⊥ u
      exact absurd (hxz.le.trans hzu) hxu.1
    · -- u ≤ z: witness w = u; u < z since u = z would give x ⊥ z contradicting x < z
      exact Or.inl ⟨u, hxu, huz.lt_of_ne (fun heq => absurd hxz.le (heq ▸ hxu.1))⟩
  · -- u ∈ incompSet y, i.e., y ⊥ u
    simp only [incompSet, Set.mem_setOf_eq] at hyu
    rcases hu_ninc with hzu | huz
    · -- z ≤ u: witness w = u; z < u since z = u would give y ⊥ z contradicting z < y
      exact Or.inr ⟨u, hzu.lt_of_ne (fun heq => absurd (heq ▸ hzy.le) hyu.2), hyu⟩
    · -- u ≤ z: then u ≤ z < y contradicts y ⊥ u
      exact absurd (huz.trans hzy.le) hyu.2
private lemma weakN_or_X_of_veryWeakN [Finite P]
    {a x y d : P} (hVW : IsVeryWeakN a x y d)
    (hfall : ∀ z : P, ¬ (incompSet x ∪ incompSet y ⊆ incompSet z)) :
    (∃ a b c d : P, IsWeakN a b c d) ∨ (∃ a b c d m : P, IsX a b c d m) := by
  haveI : Fintype P := Fintype.ofFinite P
  haveI : DecidableLT P := fun _ _ => Classical.dec _
  haveI : DecidableLE P := fun _ _ => Classical.dec _
  haveI : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder
  obtain ⟨hay, hxy, hxd, hax, hyd⟩ := hVW
  by_cases hcov : x ⋖ y
  · exact Or.inl ⟨a, x, y, d, hay, hcov, hxd, hax, hyd⟩
  · -- ¬ x ⋖ y: interior of [x,y] is nonempty
    -- Lower witnesses: all w with x ⊥ w that lie strictly below some z ∈ Ioo x y
    let L : Set P := {z | x < z ∧ z < y ∧ ∃ w, (x ⊥ w) ∧ w < z}
    by_cases hL : L = ∅
    · -- L = ∅: every z in Ioo x y has an upper witness
      -- Ioo x y is nonempty since ¬ x ⋖ y
      have hIoo_ne : (Finset.Ioo x y).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hcov (covBy_iff_Ioo_eq.mpr ⟨hxy,
          by rw [← Finset.coe_Ioo, Finset.coe_eq_empty]; exact h⟩)
      -- Take a maximal element z_max of Ioo x y
      obtain ⟨z_max, hz_max_mem, hz_max_max⟩ := (Finset.Ioo x y).exists_maximal hIoo_ne
      rw [Finset.mem_Ioo] at hz_max_mem
      obtain ⟨hxz, hzy⟩ := hz_max_mem
      -- z_max ⋖ y: any b with z_max < b < y would be in Ioo x y, contradicting maximality
      have hcov_zy : z_max ⋖ y := ⟨hzy, fun b hzb hby =>
        lt_irrefl z_max (hzb.trans_le
          (hz_max_max (Finset.mem_Ioo.mpr ⟨hxz.trans hzb, hby⟩) hzb.le))⟩
      -- z_max has an upper witness: it has no lower witness (since L = ∅)
      obtain ⟨w, hzw, hyw⟩ : ∃ w, z_max < w ∧ y ⊥ w := by
        rcases chain_claim x y hfall hxz hzy with ⟨w, hxw, hwz⟩ | ⟨w, hzw, hyw⟩
        · exact absurd (show z_max ∈ L from ⟨hxz, hzy, w, hxw, hwz⟩)
            (by simp [hL])
        · exact ⟨w, hzw, hyw⟩
      by_cases haz : a ⊥ z_max
      · -- a ⊥ z_max: IsWeakN a z_max y w
        exact Or.inl ⟨a, z_max, y, w, hay, hcov_zy, hzw, haz, hyw⟩
      · simp only [perp_iff, not_and_or, not_not] at haz
        rcases haz with haz | hza
        · rcases haz.lt_or_eq with hlt | heq
          · -- a < z_max: IsX a x y w z_max
            exact Or.inr ⟨a, x, y, w, z_max, hlt, hzy, hxz, hzw, hax, hyw⟩
          · -- a = z_max: x < z_max = a contradicts a ⊥ x
            exact absurd (heq ▸ hxz).le hax.2
        · -- z_max ≤ a: x < z_max ≤ a contradicts a ⊥ x
          exact absurd (hxz.trans_le hza).le hax.2
    · -- L ≠ ∅: take a minimal element z_min of L
      haveI : DecidablePred (· ∈ L) := fun _ => Classical.dec _
      have hLne : (Set.toFinset L).Nonempty :=
        Set.toFinset_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hL)
      obtain ⟨z_min, hz_min_mem, hz_min_min⟩ := (Set.toFinset L).exists_minimal hLne
      rw [Set.mem_toFinset] at hz_min_mem
      obtain ⟨hxz, hzy, w, hxw, hwz⟩ := hz_min_mem
      by_cases hcov_xz : x ⋖ z_min
      · -- x ⋖ z_min: three cases on z_min vs d
        by_cases hdz : z_min ⊥ d
        · -- z_min ⊥ d: IsWeakN w x z_min d
          exact Or.inl ⟨w, x, z_min, d, hwz, hcov_xz, hxd, ⟨hxw.2, hxw.1⟩, hdz⟩
        · simp only [perp_iff, not_and_or, not_not] at hdz
          rcases hdz with hzd | hdz
          · -- z_min ≤ d: strengthen to z_min < d (z_min = d gives d < y contradicting hyd)
            have hzd_strict : z_min < d := hzd.lt_of_ne
              (fun heq => absurd (heq ▸ hzy).le hyd.2)
            -- IsX w x y d z_min
            exact Or.inr ⟨w, x, y, d, z_min, hwz, hzy, hxz, hzd_strict, ⟨hxw.2, hxw.1⟩, hyd⟩
          · -- d ≤ z_min: d ≤ z_min < y contradicts y ⊥ d
            exact absurd (hdz.trans_lt hzy).le hyd.2
      · -- ¬ x ⋖ z_min: interior of [x, z_min] is nonempty
        have hIoo_ne : (Finset.Ioo x z_min).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          exact hcov_xz (covBy_iff_Ioo_eq.mpr ⟨hxz,
            by rw [← Finset.coe_Ioo, Finset.coe_eq_empty]; exact h⟩)
        obtain ⟨z_prec, hz_prec_mem, hz_prec_max⟩ :=
          (Finset.Ioo x z_min).exists_maximal hIoo_ne
        rw [Finset.mem_Ioo] at hz_prec_mem
        obtain ⟨hxzp, hzpz⟩ := hz_prec_mem
        have hcov_pz : z_prec ⋖ z_min := ⟨hzpz, fun b hzpb hbz =>
          lt_irrefl z_prec (hzpb.trans_le
            (hz_prec_max (Finset.mem_Ioo.mpr ⟨hxzp.trans hzpb, hbz⟩) hzpb.le))⟩
        -- z_prec ∉ L: z_min is minimal in L and z_prec < z_min
        have hzp_notL : z_prec ∉ L := fun hzp_in =>
          lt_irrefl z_prec (hzpz.trans_le
            (hz_min_min (Set.mem_toFinset.mpr hzp_in) hzpz.le))
        -- z_prec has an upper witness (no lower witness since z_prec ∉ L)
        obtain ⟨w_prec, hwp, hywp⟩ : ∃ w_prec, z_prec < w_prec ∧ y ⊥ w_prec := by
          rcases chain_claim x y hfall hxzp (hzpz.trans hzy) with
            ⟨w', hxw', hw'z⟩ | ⟨w', hzw', hyw'⟩
          · exact absurd (show z_prec ∈ L from ⟨hxzp, hzpz.trans hzy, w', hxw', hw'z⟩) hzp_notL
          · exact ⟨w', hzw', hyw'⟩
        -- three cases on z_min vs w_prec
        by_cases hzw_prec : z_min ⊥ w_prec
        · -- z_min ⊥ w_prec: three cases on w vs z_prec
          by_cases hwzp : w ⊥ z_prec
          · -- w ⊥ z_prec: IsWeakN w z_prec z_min w_prec
            exact Or.inl ⟨w, z_prec, z_min, w_prec, hwz, hcov_pz, hwp, hwzp, hzw_prec⟩
          · simp only [perp_iff, not_and_or, not_not] at hwzp
            rcases hwzp with hwzp | hzpw
            · -- w ≤ z_prec, hence w < z_prec (w = z_prec contradicts x ⊥ w via x < z_prec)
              have hwlt : w < z_prec := hwzp.lt_of_ne
                (fun h => absurd (h ▸ hxzp).le hxw.1)
              -- IsX w x y w_prec z_prec
              exact Or.inr ⟨w, x, y, w_prec, z_prec, hwlt, hzpz.trans hzy,
                hxzp, hwp, ⟨hxw.2, hxw.1⟩, hywp⟩
            · -- z_prec ≤ w: x < z_prec ≤ w contradicts x ⊥ w
              exact absurd (hxzp.trans_le hzpw).le hxw.1
        · simp only [perp_iff, not_and_or, not_not] at hzw_prec
          rcases hzw_prec with hzw | hwz'
          · -- z_min ≤ w_prec: strengthen to z_min < w_prec
            -- (z_min = w_prec gives w_prec ≤ y contradicting hywp)
            have hlt : z_min < w_prec := hzw.lt_of_ne
              (fun heq => absurd (heq ▸ hzy).le hywp.2)
            -- IsX w x y w_prec z_min
            exact Or.inr ⟨w, x, y, w_prec, z_min, hwz, hzy, hxz, hlt,
              ⟨hxw.2, hxw.1⟩, hywp⟩
          · -- w_prec ≤ z_min: w_prec ≤ z_min < y contradicts y ⊥ w_prec
            exact absurd (hwz'.trans_lt hzy).le hywp.2
end

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution [Finite P] :
    IsCompatible P ↔
    (¬ ∃ a b c d : P, IsWeakN a b c d) ∧
    (¬ ∃ a b c d m : P, IsX a b c d m) := by
  constructor
  · -- (b) → (a): compatible implies no weak N and no X
    intro hcomp
    exact ⟨fun ⟨a, b, c, d, hw⟩ => not_compatible_if_weakN a b c d hw hcomp,
           fun ⟨a, b, c, d, m, hx⟩ => not_compatible_if_X a b c d m hx hcomp⟩
  · -- (a) → (b): no weak N and no X implies compatible
    intro ⟨hnoN, hnoX⟩
    by_contra hnotcomp
    unfold IsCompatible at hnotcomp
    push Not at hnotcomp
    obtain ⟨x, y, hxy_comp, hfall⟩ := hnotcomp
    have hne : x ≠ y := fun heq => hfall x (heq ▸ (Set.union_self _).subset)
    simp only [perp_iff, not_and_or, not_not] at hxy_comp
    rcases hxy_comp with hle | hle
    · obtain ⟨a, d, hVW⟩ := veryWeakN_aux x y (hle.lt_of_ne hne) hfall
      rcases weakN_or_X_of_veryWeakN hVW hfall with ⟨_, _, _, _, hw⟩ | ⟨_, _, _, _, _, hx⟩
      · exact hnoN ⟨_, _, _, _, hw⟩
      · exact hnoX ⟨_, _, _, _, _, hx⟩
    · obtain ⟨a, d, hVW⟩ := veryWeakN_aux y x (hle.lt_of_ne (Ne.symm hne))
        (fun z hz => hfall z (Set.union_comm _ _ ▸ hz))
      rcases weakN_or_X_of_veryWeakN hVW (fun z hz => hfall z (Set.union_comm _ _ ▸ hz))
        with ⟨_, _, _, _, hw⟩ | ⟨_, _, _, _, _, hx⟩
      · exact hnoN ⟨_, _, _, _, hw⟩
      · exact hnoX ⟨_, _, _, _, _, hx⟩
