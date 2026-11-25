-- Prove2me | solution 1 for UpperTheory.attains_blockListOfWeights_along_orbits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:58.15726+00:00
-- url     : https://prove2.me/submissions/67c7037b-2b20-4aed-a611-b17c24d9d680

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_RowDefs
import Definitions.Def_Formalism_DropLevelBounds_ThBounds
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Development_AutomorphicArithmetic_OrbitLabellings_AttainsBlockListOfWeightsAlongOrbits
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2
namespace UpperTheory.G2.RowPlan
private theorem cast_eq {d : ℕ} (hd : Odd d) (x y : ℕ) :
    (x : ZMod (2 * d)) = y ↔ x % 2 = y % 2 ∧ (x : ZMod d) = y := by
  rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff,
    ← Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_two_left).2 hd)]
  rfl
private theorem ev_iff {d : ℕ} [NeZero d] (hd : Odd d) (ev : ZMod d → ZMod (2 * d))
    (hev : ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a) (s : ZMod (2 * d)) (a : ZMod d) :
    s = ev a ↔ Even s.val ∧ a = ((s.val : ℕ) : ZMod d) := by
  constructor
  · rintro rfl
    exact ⟨(hev a).1, (hev a).2.symm⟩
  · rintro ⟨he, ha⟩
    haveI : NeZero (2 * d) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne d)⟩
    have key : ((s.val : ℕ) : ZMod (2 * d)) = (((ev a).val : ℕ) : ZMod (2 * d)) := by
      rw [cast_eq hd]
      exact ⟨by rw [Nat.even_iff.1 he, Nat.even_iff.1 (hev a).1], by rw [(hev a).2, ha]⟩
    simpa only [ZMod.natCast_zmod_val] using key
private theorem cast_val_eq_castHom_of_double {d : ℕ} [NeZero d] (x : ZMod (2 * d)) :
    ((x.val : ℕ) : ZMod d) = ZMod.castHom (dvd_mul_left d 2) (ZMod d) x := by
  haveI : NeZero (2 * d) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne d)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
private theorem cast_val_two_eq_castHom_of_double {d : ℕ} [NeZero d] (x : ZMod (2 * d)) :
    ((x.val : ℕ) : ZMod 2) = ZMod.castHom (dvd_mul_right 2 d) (ZMod 2) x := by
  haveI : NeZero (2 * d) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne d)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
private theorem ev_iff' {d : ℕ} [NeZero d] (hd : Odd d) (ev : ZMod d → ZMod (2 * d))
    (hev : ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a) (s : ZMod (2 * d)) (a : ZMod d) (i : ℕ)
    (hi : Odd i) :
    s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) ↔
      Even s.val ∧ a = ((s.val : ℕ) : ZMod d) - (i : ZMod d) := by
  have h1 : s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) ↔ s + (d : ZMod (2 * d)) - i = ev a := by
    constructor
    · intro h
      rw [h, add_sub_cancel_right]
    · intro h
      rw [← h, sub_add_cancel]
  rw [h1, ev_iff hd ev hev]
  have hpar : Even (s + (d : ZMod (2 * d)) - i).val ↔ Even s.val := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even, cast_val_two_eq_castHom_of_double, cast_val_two_eq_castHom_of_double, map_sub,
      map_add, map_natCast, map_natCast, ZMod.natCast_eq_one_iff_odd.2 hd, ZMod.natCast_eq_one_iff_odd.2 hi,
      add_sub_cancel_right]
  have hres : (((s + (d : ZMod (2 * d)) - i).val : ℕ) : ZMod d) = ((s.val : ℕ) : ZMod d) - i := by
    rw [cast_val_eq_castHom_of_double, cast_val_eq_castHom_of_double, map_sub, map_add, map_natCast, map_natCast, ZMod.natCast_self, add_zero]
  rw [hpar, hres]
private theorem least_level_odd (k l : ℕ) (hl : 2 ≤ l) : Odd (RF.i0 k l) := by
  unfold RF.i0
  have hne : ({i | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ (3 / 2 : ℝ) < (l : ℝ) ^ i} : Set ℕ).Nonempty := by
    refine ⟨2 * k + 3, ⟨k + 1, by ring⟩, by omega, ?_⟩
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((k : ℝ) + 1) ^ (2 : ℝ) := by
      calc (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((k : ℝ) + 1) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow hk0 (by linarith) (by norm_num)
        _ ≤ ((k : ℝ) + 1) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h2 : ((k : ℝ) + 1) ^ (2 : ℝ) = (((k + 1) ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_two]
      push_cast
      ring
    have h3 : (k + 1) ^ 2 < 2 ^ (2 * k + 3) := by
      have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      calc (k + 1) ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hk 2
        _ = 2 ^ (2 * k) := by rw [← pow_mul, mul_comm]
        _ < 2 ^ (2 * k + 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ (2 * k + 3) ≤ (l : ℝ) ^ (2 * k + 3) :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hl) _
    have h5 : (((k + 1) ^ 2 : ℕ) : ℝ) < (2 : ℝ) ^ (2 * k + 3) := by exact_mod_cast h3
    linarith
  exact (Nat.sInf_mem hne).1
private theorem card_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) : Z.card * P.d = Fintype.card P.Pl := by
  unfold RF.IsReps at h
  let f : ↥Z × ZMod P.d → P.Pl := fun p => P.pos p.1.1 p.2.val
  have hbij : Function.Bijective f := by
    constructor
    · intro p q hpq
      obtain ⟨r, -, hr⟩ := h (f q)
      have e1 := hr (p.1.1, p.2) ⟨p.1.2, hpq⟩
      have e2 := hr (q.1.1, q.2) ⟨q.1.2, rfl⟩
      have e3 : ((p.1.1, p.2) : P.Pl × ZMod P.d) = (q.1.1, q.2) := e1.trans e2.symm
      simp only [Prod.mk.injEq] at e3
      exact Prod.ext (Subtype.ext e3.1) e3.2
    · intro z
      obtain ⟨r, ⟨hr1, hr2⟩, -⟩ := h z
      exact ⟨(⟨r.1, hr1⟩, r.2), hr2⟩
  rw [← Fintype.card_of_bijective hbij, Fintype.card_prod, Fintype.card_coe, ZMod.card]
variable {d : ℕ} [NeZero d]
private theorem sum_supp {M : Type} [AddCommMonoid M] (y : ZMod d → ℕ → ℕ) (f : ZMod d → ℕ → ℕ → M)
    (hf : ∀ a i, f a i 0 = 0) :
    ∑ x ∈ supp y, f x.1 x.2 (y x.1 x.2) = ∑ a, ∑ i ∈ oddLevels d, f a i (y a i) := by
  unfold supp
  rw [Finset.sum_filter_of_ne, Finset.sum_product]
  intro x _ hx hy
  apply hx
  rw [hy, hf]
private theorem card_supp (y : ZMod d → ℕ → ℕ) (M : ℕ) (h : ∀ a i, 2 * M + 1 ≤ i → y a i = 0) :
    (supp y).card ≤ d * M := by
  have hsub : supp y ⊆ Finset.univ ×ˢ ((Finset.range M).image fun j => 2 * j + 1) := by
    intro x hx
    unfold supp at hx
    rw [Finset.mem_filter, Finset.mem_product] at hx
    obtain ⟨⟨-, hodd⟩, hy⟩ := hx
    unfold oddLevels at hodd
    rw [Finset.mem_filter] at hodd
    obtain ⟨j, hj⟩ := hodd.2
    rw [Finset.mem_product]
    refine ⟨Finset.mem_univ _, Finset.mem_image.2 ⟨j, Finset.mem_range.2 ?_, hj.symm⟩⟩
    by_contra hjM
    exact hy (h x.1 x.2 (by omega))
  calc (supp y).card ≤ (Finset.univ ×ˢ ((Finset.range M).image fun j => 2 * j + 1)).card :=
        Finset.card_le_card hsub
    _ = d * M := by
      rw [Finset.card_product, Finset.card_univ, ZMod.card,
        Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), Finset.card_range]
variable {C : Type} [Field C] {V : VF C} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
private theorem rk_le (X : RowData C V (2 * d) I J) (g : Fin 2) (a : ZMod (2 * d)) :
    X.rkF g a ≤ X.n + (X.j + X.j') := by
  unfold RowData.rkF
  by_cases h : X.big g a
  · rw [X.rk_big g a h]
    omega
  · rw [X.rk_small g a h]
    omega
private theorem deg_le (X : RowData C V (2 * d) I J) (n K : ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (s : ZMod (2 * d)) :
    (RF.monDegAll X 0 (rst n ga s) K : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) := by
  unfold RF.monDegAll
  rw [Finset.sum_eq_single s (fun b _ hb => by simp [monDeg, rst, hb]) (by simp)]
  unfold monDeg
  push_cast
  calc ∑ k ∈ Finset.Icc 1 (min K (X.rkF 0 s)), (k : ℝ) * (rst n ga s s k : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 K, (k : ℝ) * (rst n ga s s k : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk ⊢
          exact ⟨hk.1, le_trans hk.2 (min_le_left _ _)⟩
        · intro k _ _
          positivity
    _ = ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [rst, if_true]
        split_ifs <;> simp
    _ ≤ _ := le_refl _
private theorem blocks_rows (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d)) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K M : ℕ) (h : ∀ a i, 2 * M + 1 ≤ i → y a i = 0) :
    ((blocks X ev y u ga K).map fun q => q.1.what₂ X.n).sum ≤ d * ((M + 1) * X.n + 2 * K) := by
  simp only [blocks, List.map_append, List.sum_append, List.map_map,
    Finset.sum_map_toList, Function.comp_def, RF.GlobalTheory.what₂, Finset.sum_const, smul_eq_mul, Finset.card_univ, ZMod.card]
  have h1 := Nat.mul_le_mul_right X.n (card_supp y M h)
  nlinarith
private theorem blocks_bd (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d)) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K : ℕ) (hl : 2 ≤ V.l) :
    ((blocks X ev y u ga K).map Prod.snd).sum ≤
      ((∑ a, ∑ i ∈ oddLevels d, RF.blockBd V.l X.n X.m i (y a i)) + ∑ a, RF.chBd V.l X.n X.m (u a)) +
        (∑ s : ZMod (2 * d), ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = X.n then (0 : ℝ) else (k : ℝ) * ga s k)) /
          ((V.l : ℝ) - 1) := by
  simp only [blocks, List.map_append, List.sum_append, List.map_map, Function.comp_def, Finset.sum_map_toList]
  have hs := sum_supp y (fun _ i v => RF.blockBd V.l X.n X.m i v) (fun a i => by simp [RF.blockBd])
  have hpos : (0 : ℝ) < (V.l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (V.l : ℝ) := by exact_mod_cast hl
    linarith
  have hD : ∑ s : ZMod (2 * d), (RF.monDegAll X 0 (rst X.n ga s) K : ℝ) / ((V.l : ℝ) - 1) ≤
      (∑ s : ZMod (2 * d), ∑ k ∈ Finset.Icc 1 K, (if Even s.val ∧ k = X.n then (0 : ℝ) else (k : ℝ) * ga s k)) /
        ((V.l : ℝ) - 1) := by
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun s _ => deg_le X X.n K ga s) hpos.le
  linarith
private theorem blocks_wt (hd : Odd d) (X : RowData C V (2 * d) I J) (ev : ZMod d → ZMod (2 * d))
    (hev : ∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod d) = a) (y : ZMod d → ℕ → ℕ)
    (u : ZMod d → ℕ) (ga : ZMod (2 * d) → ℕ → ℕ) (K : ℕ) (hK : X.n + (X.j + X.j') ≤ K) (W : ZMod d → ℕ)
    (hs : ∀ s k, ga s k ≠ 0 → 1 ≤ k ∧ k ≤ X.rkF 0 s)
    (hm : ∀ s : ZMod (2 * d), Even s.val → ga s X.n = W ((s.val : ℕ) : ZMod d))
    (hb : ∀ a, W a = (∑ i ∈ oddLevels d, V.l ^ i * y a i) + (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) + u a)
    (s : ZMod (2 * d)) (k : ℕ) :
    ((blocks X ev y u ga K).map fun q => q.1.wt X 0 s k + q.1.wt X 1 (s + (d : ZMod (2 * d))) k).sum = ga s k := by
  have hrk : ∀ a, X.rkF 0 a ≤ K := fun a => le_trans (rk_le X 0 a) hK
  simp only [blocks, List.map_append, List.sum_append, List.map_map]
  rw [Finset.sum_map_toList, Finset.sum_map_toList, Finset.sum_map_toList]
  simp [Function.comp_def, RF.GlobalTheory.wt, rst]
  have hfirst : (if 1 ≤ k ∧ k ≤ K ∧ k ≤ X.rkF 0 s then ga s k else 0) = ga s k := by
    split_ifs with h
    · rfl
    · by_contra hne
      have h' := hs s k (Ne.symm hne)
      exact h ⟨h'.1, le_trans h'.2 (hrk s), h'.2⟩
  have hodd : ∀ i ∈ oddLevels d, Odd i := by
    intro i hi
    unfold oddLevels at hi
    exact (Finset.mem_filter.1 hi).2
  by_cases hkn : k = X.n
  swap
  · simp only [hkn, and_false, if_false, Finset.sum_const_zero, add_zero]
    exact hfirst
  subst hkn
  simp only [and_true]
  by_cases he : Even s.val
  · have hch : ∀ a, (s = ev a ↔ a = ((s.val : ℕ) : ZMod d)) := fun a => by
      rw [ev_iff hd ev hev s a]
      simp [he]
    have hbi : ∀ a (i : ℕ), Odd i →
        (s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) ↔ a = ((s.val : ℕ) : ZMod d) - (i : ZMod d)) :=
      fun a i hi => by
        rw [ev_iff' hd ev hev s a i hi]
        simp [he]
    have e1 := sum_supp y (fun a i v => if s = ev a then V.l ^ i * v else 0) (fun a i => by simp)
    have e2 := sum_supp y (fun a i v => if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then v else 0)
      (fun a i => by simp)
    rw [Finset.sum_add_distrib, e1, e2]
    have t0 : (if 1 ≤ X.n ∧ X.n ≤ K ∧ X.n ≤ X.rkF 0 s then (if Even s.val then 0 else ga s X.n) else 0) = 0 := by
      simp [he]
    have t1 : (∑ x, if s = ev x then u x else 0) = u ((s.val : ℕ) : ZMod d) := by
      simp_rw [hch]
      simp
    have t2 : (∑ a, ∑ i ∈ oddLevels d, if s = ev a then V.l ^ i * y a i else 0) =
        ∑ i ∈ oddLevels d, V.l ^ i * y ((s.val : ℕ) : ZMod d) i := by
      simp_rw [hch]
      rw [Finset.sum_comm]
      simp
    have t3 : (∑ a, ∑ i ∈ oddLevels d, if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then y a i else 0) =
        ∑ i ∈ oddLevels d, y (((s.val : ℕ) : ZMod d) - (i : ZMod d)) i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      simp_rw [hbi _ i (hodd i hi)]
      simp
    rw [t0, t1, t2, t3, hm s he, hb]
    ring
  · have hch0 : ∀ a, ¬ s = ev a := fun a h => he (by rw [h]; exact (hev a).1)
    have t3 : (∑ a, ∑ i ∈ oddLevels d, if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then y a i else 0) = 0 :=
      Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun i hi =>
        if_neg (fun h => he ((ev_iff' hd ev hev s a i (hodd i hi)).1 h).1)))
    have e2 := sum_supp y (fun a i v => if s + (d : ZMod (2 * d)) = ev a + (i : ZMod (2 * d)) then v else 0)
      (fun a i => by simp)
    rw [Finset.sum_add_distrib, e2, t3]
    simpa [hch0, he] using hfirst
end UpperTheory.G2.RowPlan
end

set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral UpperTheory.G2
open UpperTheory.G2.RowPlan
namespace UpperTheory
theorem _root_.solution :
    RF.CHSupply → RF.MONSupply → ∀ (P : RF.Par) (l : ℕ) (C1 : ℝ), Fintype.card P.Pl = P.f → 1 ≤ P.m → P.m + 3 ≤ P.k → P.r = P.k - 1 + P.m → 5 ≤ l →
    ∀ (Pk : PkgCs P l C1) (y : P.Pl → ZMod P.d → ℕ → ℕ) (u : P.Pl → ZMod P.d → ℕ) (ev : ZMod P.d → ZMod (2 * P.d)),
    (∀ a, Even (ev a).val ∧ (((ev a).val : ℕ) : ZMod P.d) = a) →
    (∀ z ∈ Pk.Z, ∀ a, RF.alongOrb P z Pk.W a = (∑ i ∈ oddLevels P.d, l ^ i * y z a i) +
      (∑ i ∈ oddLevels P.d, y z (a - (i : ZMod P.d)) i) + u z a) →
    (∀ z ∈ Pk.Z, ∀ a i, RF.i0 P.k l ≤ i → y z a i = 0) →
    (∀ (o : {z // z ∈ Pk.Z}) a, ∀ i ∈ oddLevels P.d, y o.1 a i ≠ 0 →
      (RF.GlobalTheory.bi 0 (ev a) i (y o.1 a i)).Attains (Pk.R.X o) (Pk.R.F o) (RF.blockBd l (P.k - 1) P.m i (y o.1 a i))) →
    Pk.ν ≤ (∑ z ∈ Pk.Z, ((∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y z a i)) + ∑ a, RF.chBd l (P.k - 1) P.m (u z a))) +
      Pk.rest / ((l : ℝ) - 1) := by
  intro hCH hM P l C1 hf hm1 hmk hr hl5 Pk y u ev hev hW hy hbi
  have hd : Odd P.d := Pk.odd
  have hn1 : ∀ o, (Pk.R.X o).n = P.k - 1 := fun o => (Pk.R.hn o).1
  have hn2 : ∀ o, (Pk.R.X o).m = P.m := fun o => (Pk.R.hn o).2
  have hVl : Pk.R.V.l = l := Pk.R.hVl
  obtain ⟨M, hMe⟩ := least_level_odd P.k l (by omega)
  let L : ↥Pk.Z → List (RF.GlobalTheory (2 * P.d) × ℝ) := fun o =>
    blocks (Pk.R.X o) ev (y o.1) (u o.1) (Pk.ga o) P.r
  have hv := Pk.val L ?_ ?_ ?_ ?_
  · refine le_trans hv ?_
    calc ∑ o, (List.map Prod.snd (L o)).sum
        ≤ ∑ o : ↥Pk.Z, (((∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y o.1 a i)) +
            ∑ a, RF.chBd l (P.k - 1) P.m (u o.1 a)) +
            (∑ s : ZMod (2 * P.d), ∑ k ∈ Finset.Icc 1 P.r,
              (if Even s.val ∧ k = P.k - 1 then (0 : ℝ) else (k : ℝ) * Pk.ga o s k)) / ((l : ℝ) - 1)) := by
          apply Finset.sum_le_sum
          intro o _
          have := blocks_bd (Pk.R.X o) ev (y o.1) (u o.1) (Pk.ga o) P.r (by rw [hVl]; omega)
          rwa [hn1 o, hn2 o, hVl] at this
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, Pk.rest_eq]
          congr 1
          exact Finset.sum_coe_sort Pk.Z (fun z => (∑ a, ∑ i ∈ oddLevels P.d, RF.blockBd l (P.k - 1) P.m i (y z a i)) +
            ∑ a, RF.chBd l (P.k - 1) P.m (u z a))
  · intro o q hq
    simp only [L, blocks, List.mem_append, List.mem_map, Finset.mem_toList] at hq
    rcases hq with ⟨s, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨x, hx, rfl⟩
    · exact (hM _ _ _ _ _ (Pk.R.X o) (Pk.R.F o) 0 _ P.r).1
    · have hbig : (Pk.R.X o).big 0 (ev a) := ((Pk.R.alt o).2 (ev a)).2 (hev a).1
      exact (hCH _ _ _ _ _ (Pk.R.X o) (Pk.R.F o) 0 (ev a) hbig (u o.1 a)).1 (Pk.R.alt o)
    · simp only [supp, Finset.mem_filter, Finset.mem_product] at hx
      have := hbi o x.1 x.2 hx.1.2 hx.2
      rwa [hn1 o, hn2 o, hVl]
  · intro o q hq g e N hqe
    simp only [L, blocks, List.mem_append, List.mem_map, Finset.mem_toList] at hq
    rcases hq with ⟨s, -, rfl⟩ | ⟨a, -, rfl⟩ | ⟨x, hx, rfl⟩
    · obtain ⟨-, rfl, -⟩ := RF.GlobalTheory.mon.inj hqe
      exact ⟨s, fun a k ha => by simp [rst, ha]⟩
    · cases hqe
    · cases hqe
  · have hrow : ∀ o, (List.map (fun q => RF.GlobalTheory.what₂ (Pk.R.X o).n q.1) (L o)).sum ≤
        P.d * ((M + 1) * (P.k - 1) + 2 * P.r) := by
      intro o
      have := blocks_rows (Pk.R.X o) ev (y o.1) (u o.1) (Pk.ga o) P.r M
        (fun a i hi => hy o.1 o.2 a i (by omega))
      rw [hn1 o] at this
      rw [hn1 o]
      exact this
    have hZ := card_reps P Pk.Z Pk.hZ
    rw [hf] at hZ
    calc 2 * ∑ o, (List.map (fun q => RF.GlobalTheory.what₂ (Pk.R.X o).n q.1) (L o)).sum
        ≤ 2 * ∑ o : ↥Pk.Z, P.d * ((M + 1) * (P.k - 1) + 2 * P.r) := by
          gcongr with o
          exact hrow o
      _ = P.f * ((RF.i0 P.k l + 1) * (P.k - 1) + 4 * P.r) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, ← hZ, hMe]
          ring
      _ ≤ Pk.nW := Pk.what₂
  · intro o s k
    have hK : (Pk.R.X o).n + ((Pk.R.X o).j + (Pk.R.X o).j') ≤ P.r := by
      have e : (Pk.R.X o).m = (Pk.R.X o).j + (Pk.R.X o).j' := rfl
      rw [← e, hn1 o, hn2 o]
      omega
    exact blocks_wt hd (Pk.R.X o) ev hev (y o.1) (u o.1) (Pk.ga o) P.r hK
      (fun a => RF.alongOrb P o.1 Pk.W a) (Pk.supp o)
      (fun s hs => by
        rw [hn1 o, Pk.main o s hs]
        simp only [RF.alongOrb, ZMod.val_natCast])
      (fun a => by
        rw [hVl]
        exact hW o.1 o.2 a) s k
end UpperTheory
