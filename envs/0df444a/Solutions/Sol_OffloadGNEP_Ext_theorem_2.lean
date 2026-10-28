-- Prove2me | solution 1 for OffloadGNEP.Ext.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T16:19:20.131556+00:00
-- url     : https://prove2.me/submissions/f1a82d2e-b2a5-4ed8-bbbf-de8706694738

import Mathlib
import Definitions.Def_OffloadGNEP_Ext_Setting

set_option autoImplicit false

namespace OffloadT2

open OffloadGNEP.Ext
open OffloadGNEP.Exist (Tier pair)

lemma sum_tier (f : Tier → ℝ) : ∑ i, f i = f .m + f .clet + f .cloud := by
  have h : (Finset.univ : Finset Tier) = {Tier.m, Tier.clet, Tier.cloud} := rfl
  rw [h, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

lemma mem_Kprod {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) :
    x ∈ Kprod P ↔ ∀ u, x u ∈ Ktil P u := Iff.rfl

/-! ### The scalar model of one user's objective -/

noncomputable def Phi (al be ga de c a r m cl k : ℝ) : ℝ :=
  al * m / (1 - al * m) + be * cl + ga * k + de * cl / (c - a * cl) + r * (a * cl)

lemma piece_m (al m0 m1 : ℝ) (hp : 1 - al * m0 ≠ 0) (hq : 1 - al * m1 ≠ 0) :
    al * m1 / (1 - al * m1) - al * m0 / (1 - al * m0) - al / (1 - al * m0) ^ 2 * (m1 - m0)
      = al ^ 2 * (m1 - m0) ^ 2 / ((1 - al * m0) ^ 2 * (1 - al * m1)) := by
  field_simp
  ring

lemma piece_c (de c a c0 c1 : ℝ) (hd0 : c - a * c0 ≠ 0) (hd1 : c - a * c1 ≠ 0) :
    de * c1 / (c - a * c1) - de * c0 / (c - a * c0) - de * c / (c - a * c0) ^ 2 * (c1 - c0)
      = de * c * a * (c1 - c0) ^ 2 / ((c - a * c0) ^ 2 * (c - a * c1)) := by
  rw [div_sub_div _ _ hd1 hd0, div_mul_eq_mul_div,
    div_sub_div _ _ (mul_ne_zero hd1 hd0) (pow_ne_zero 2 hd0),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hd1 hd0) (pow_ne_zero 2 hd0))
      (mul_ne_zero (pow_ne_zero 2 hd0) hd1)]
  ring

lemma key_id (al be ga de c a r m0 c0 k0 m1 c1 k1 : ℝ)
    (hp : 1 - al * m0 ≠ 0) (hq : 1 - al * m1 ≠ 0) (hd0 : c - a * c0 ≠ 0) (hd1 : c - a * c1 ≠ 0) :
    Phi al be ga de c a r m1 c1 k1 - Phi al be ga de c a r m0 c0 k0 -
      (al / (1 - al * m0) ^ 2 * (m1 - m0) + (be + de * c / (c - a * c0) ^ 2 + r * a) * (c1 - c0)
        + ga * (k1 - k0))
    = al ^ 2 * (m1 - m0) ^ 2 / ((1 - al * m0) ^ 2 * (1 - al * m1))
      + de * c * a * (c1 - c0) ^ 2 / ((c - a * c0) ^ 2 * (c - a * c1)) := by
  rw [← piece_m al m0 m1 hp hq, ← piece_c de c a c0 c1 hd0 hd1]
  unfold Phi
  ring

lemma scalar_suff (al be ga de c a r m0 c0 k0 m1 c1 k1 : ℝ)
    (hp : 0 < 1 - al * m0) (hq : 0 < 1 - al * m1) (hd0 : 0 < c - a * c0) (hd1 : 0 < c - a * c1)
    (hB : 0 ≤ de * c * a) :
    al / (1 - al * m0) ^ 2 * (m1 - m0) + (be + de * c / (c - a * c0) ^ 2 + r * a) * (c1 - c0)
        + ga * (k1 - k0) ≤
    Phi al be ga de c a r m1 c1 k1 - Phi al be ga de c a r m0 c0 k0 := by
  have h := key_id al be ga de c a r m0 c0 k0 m1 c1 k1 hp.ne' hq.ne' hd0.ne' hd1.ne'
  have h1 : 0 ≤ al ^ 2 * (m1 - m0) ^ 2 / ((1 - al * m0) ^ 2 * (1 - al * m1)) :=
    div_nonneg (by positivity) (mul_nonneg (sq_nonneg _) hq.le)
  have h2 : 0 ≤ de * c * a * (c1 - c0) ^ 2 / ((c - a * c0) ^ 2 * (c - a * c1)) :=
    div_nonneg (mul_nonneg hB (sq_nonneg _)) (mul_nonneg (sq_nonneg _) hd1.le)
  linarith

lemma inv_comb_le {p q t : ℝ} (hp : 0 < p) (hq : 0 < q) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 / (t * q + (1 - t) * p) ≤ 1 / p + 1 / q := by
  have hp' := one_div_pos.2 hp
  have hq' := one_div_pos.2 hq
  rcases le_total p q with h | h
  · have h2 : p ≤ t * q + (1 - t) * p := by nlinarith
    have := one_div_le_one_div_of_le hp h2
    linarith
  · have h2 : q ≤ t * q + (1 - t) * p := by nlinarith
    have := one_div_le_one_div_of_le hq h2
    linarith

lemma lin_nonneg {L M : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ t * L + t ^ 2 * M) : 0 ≤ L := by
  by_contra hL
  push_neg at hL
  have hA0 : 0 < |M| + 1 := by positivity
  have hden : 0 < -L + (|M| + 1) := by linarith
  have ht0 : 0 < -L / (-L + (|M| + 1)) := div_pos (by linarith) hden
  have ht1 : -L / (-L + (|M| + 1)) ≤ 1 := by rw [div_le_one hden]; linarith
  set t := -L / (-L + (|M| + 1)) with ht
  have htA : t * (|M| + 1) < -L := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [mul_pos (neg_pos.2 hL) (neg_pos.2 hL)]
  have hM : M ≤ |M| + 1 := by have := le_abs_self M; linarith
  have h3 : t ^ 2 * M ≤ t ^ 2 * (|M| + 1) := mul_le_mul_of_nonneg_left hM (sq_nonneg t)
  have h4 := h t ht0 ht1
  nlinarith [mul_pos ht0 (show 0 < -L - t * (|M| + 1) by linarith)]

lemma scalar_nec (al be ga de c a r m0 c0 k0 m1 c1 k1 : ℝ)
    (hp : 0 < 1 - al * m0) (hq : 0 < 1 - al * m1) (hd0 : 0 < c - a * c0) (hd1 : 0 < c - a * c1)
    (hB : 0 ≤ de * c * a)
    (hmin : ∀ t : ℝ, 0 < t → t ≤ 1 →
      Phi al be ga de c a r m0 c0 k0 ≤
        Phi al be ga de c a r (t * m1 + (1 - t) * m0) (t * c1 + (1 - t) * c0)
          (t * k1 + (1 - t) * k0)) :
    0 ≤ al / (1 - al * m0) ^ 2 * (m1 - m0) + (be + de * c / (c - a * c0) ^ 2 + r * a) * (c1 - c0)
        + ga * (k1 - k0) := by
  have A0 : 0 ≤ al ^ 2 * (m1 - m0) ^ 2 / (1 - al * m0) ^ 2 := by positivity
  have B0 : 0 ≤ de * c * a * (c1 - c0) ^ 2 / (c - a * c0) ^ 2 :=
    div_nonneg (mul_nonneg hB (sq_nonneg _)) (sq_nonneg _)
  apply lin_nonneg (M := al ^ 2 * (m1 - m0) ^ 2 / (1 - al * m0) ^ 2 *
      (1 / (1 - al * m0) + 1 / (1 - al * m1)) +
      de * c * a * (c1 - c0) ^ 2 / (c - a * c0) ^ 2 * (1 / (c - a * c0) + 1 / (c - a * c1)))
  intro t ht0 ht1
  have hqt : 1 - al * (t * m1 + (1 - t) * m0) = t * (1 - al * m1) + (1 - t) * (1 - al * m0) := by
    ring
  have hdt : c - a * (t * c1 + (1 - t) * c0) = t * (c - a * c1) + (1 - t) * (c - a * c0) := by
    ring
  have hqt0 : 0 < t * (1 - al * m1) + (1 - t) * (1 - al * m0) := by nlinarith
  have hdt0 : 0 < t * (c - a * c1) + (1 - t) * (c - a * c0) := by nlinarith
  have h := key_id al be ga de c a r m0 c0 k0 (t * m1 + (1 - t) * m0) (t * c1 + (1 - t) * c0)
    (t * k1 + (1 - t) * k0) hp.ne' (by rw [hqt]; exact hqt0.ne') hd0.ne' (by rw [hdt]; exact hdt0.ne')
  have hm := hmin t ht0 ht1
  rw [hqt, hdt] at h
  have e1 : al ^ 2 * (t * m1 + (1 - t) * m0 - m0) ^ 2 /
      ((1 - al * m0) ^ 2 * (t * (1 - al * m1) + (1 - t) * (1 - al * m0)))
      = t ^ 2 * (al ^ 2 * (m1 - m0) ^ 2 / (1 - al * m0) ^ 2) *
        (1 / (t * (1 - al * m1) + (1 - t) * (1 - al * m0))) := by
    field_simp
    ring
  have e2 : de * c * a * (t * c1 + (1 - t) * c0 - c0) ^ 2 /
      ((c - a * c0) ^ 2 * (t * (c - a * c1) + (1 - t) * (c - a * c0)))
      = t ^ 2 * (de * c * a * (c1 - c0) ^ 2 / (c - a * c0) ^ 2) *
        (1 / (t * (c - a * c1) + (1 - t) * (c - a * c0))) := by
    field_simp
    ring
  have hlin : al / (1 - al * m0) ^ 2 * (t * m1 + (1 - t) * m0 - m0) +
      (be + de * c / (c - a * c0) ^ 2 + r * a) * (t * c1 + (1 - t) * c0 - c0) +
      ga * (t * k1 + (1 - t) * k0 - k0) =
      t * (al / (1 - al * m0) ^ 2 * (m1 - m0) +
        (be + de * c / (c - a * c0) ^ 2 + r * a) * (c1 - c0) + ga * (k1 - k0)) := by
    ring
  rw [hlin, e1, e2] at h
  have i1 := inv_comb_le hp hq ht0.le ht1
  have i2 := inv_comb_le hd0 hd1 ht0.le ht1
  have j1 := mul_le_mul_of_nonneg_left i1 (mul_nonneg (sq_nonneg t) A0)
  have j2 := mul_le_mul_of_nonneg_left i2 (mul_nonneg (sq_nonneg t) B0)
  have hM : t ^ 2 * (al ^ 2 * (m1 - m0) ^ 2 / (1 - al * m0) ^ 2 *
      (1 / (1 - al * m0) + 1 / (1 - al * m1)) +
      de * c * a * (c1 - c0) ^ 2 / (c - a * c0) ^ 2 * (1 / (c - a * c0) + 1 / (c - a * c1))) =
      t ^ 2 * (al ^ 2 * (m1 - m0) ^ 2 / (1 - al * m0) ^ 2) *
        (1 / (1 - al * m0) + 1 / (1 - al * m1)) +
      t ^ 2 * (de * c * a * (c1 - c0) ^ 2 / (c - a * c0) ^ 2) *
        (1 / (c - a * c0) + 1 / (c - a * c1)) := by ring
  rw [hM]
  linarith

/-! ### One user's objective in the scalar model -/

noncomputable def Cc {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) : ℝ :=
  1 - (1 / (P.n : ℝ)) * ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet

lemma D_eq {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) :
    D P x = Cc P u x - P.delta u / (P.n : ℝ) * x u .clet := by
  unfold D load Cc
  rw [← Finset.add_sum_erase Finset.univ (fun v => P.delta v * x v .clet) (Finset.mem_univ u)]
  ring

lemma Cc_update {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) (y : Tier → ℝ) :
    Cc P u (Function.update x u y) = Cc P u x := by
  unfold Cc
  congr 2
  apply Finset.sum_congr rfl
  intro v hv
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]

lemma D_update {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) (y : Tier → ℝ) :
    D P (Function.update x u y) = Cc P u x - P.delta u / (P.n : ℝ) * y .clet := by
  rw [D_eq P u, Cc_update, Function.update_self]

lemma cost_update {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) (y : Tier → ℝ) :
    cost P u (Function.update x u y) =
      P.alpha u * y .m / (1 - P.alpha u * y .m) + P.beta u * y .clet + P.gamma u * y .cloud +
        P.delta u * y .clet / (Cc P u x - P.delta u / (P.n : ℝ) * y .clet) := by
  unfold cost
  rw [D_update]
  simp only [Function.update_self]

lemma cost_self {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) :
    cost P u x =
      P.alpha u * x u .m / (1 - P.alpha u * x u .m) + P.beta u * x u .clet +
        P.gamma u * x u .cloud +
        P.delta u * x u .clet / (Cc P u x - P.delta u / (P.n : ℝ) * x u .clet) := by
  have h := cost_update P u x (x u)
  rwa [Function.update_eq_self] at h

lemma Phi_upd {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) (y : Tier → ℝ) (r : ℝ) :
    cost P u (Function.update x u y) + r * (P.delta u / (P.n : ℝ) * y .clet) =
      Phi (P.alpha u) (P.beta u) (P.gamma u) (P.delta u) (Cc P u x) (P.delta u / (P.n : ℝ)) r
        (y .m) (y .clet) (y .cloud) := by
  rw [cost_update]
  rfl

lemma Phi_self {N : ℕ} (P : Params N) (u : Fin N) (x : Fin N → Tier → ℝ) (r : ℝ) :
    cost P u x + r * (P.delta u / (P.n : ℝ) * x u .clet) =
      Phi (P.alpha u) (P.beta u) (P.gamma u) (P.delta u) (Cc P u x) (P.delta u / (P.n : ℝ)) r
        (x u .m) (x u .clet) (x u .cloud) := by
  rw [cost_self]
  rfl

lemma F_m {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) (u : Fin N) :
    F P x u .m = P.alpha u / (1 - P.alpha u * x u .m) ^ 2 := rfl

lemma F_cloud {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) (u : Fin N) :
    F P x u .cloud = P.gamma u := rfl

lemma F_clet {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) (u : Fin N) :
    F P x u .clet = P.beta u + P.delta u * Cc P u x /
      (Cc P u x - P.delta u / (P.n : ℝ) * x u .clet) ^ 2 := by
  rw [← D_eq]
  rfl

lemma price_m {N : ℕ} (P : Params N) (r : ℝ) (u : Fin N) : price P r u .m = 0 := by
  simp [price]

lemma price_cloud {N : ℕ} (P : Params N) (r : ℝ) (u : Fin N) : price P r u .cloud = 0 := by
  simp [price]

lemma price_clet {N : ℕ} (P : Params N) (r : ℝ) (u : Fin N) :
    price P r u .clet = r * (P.delta u / (P.n : ℝ)) := by
  simp [price]

lemma grad_eq {N : ℕ} (P : Params N) (x : Fin N → Tier → ℝ) (u : Fin N) (y : Tier → ℝ) (r : ℝ) :
    ∑ i, (F P x + price P r) u i * (y i - x u i) =
      P.alpha u / (1 - P.alpha u * x u .m) ^ 2 * (y .m - x u .m) +
        (P.beta u + P.delta u * Cc P u x / (Cc P u x - P.delta u / (P.n : ℝ) * x u .clet) ^ 2 +
          r * (P.delta u / (P.n : ℝ))) * (y .clet - x u .clet) +
        P.gamma u * (y .cloud - x u .cloud) := by
  rw [sum_tier]
  simp only [Pi.add_apply]
  rw [F_m, F_clet, F_cloud, price_m, price_clet, price_cloud]
  ring

/-! ### Pairing and load identities -/

lemma pair_update {N : ℕ} (G x : Fin N → Tier → ℝ) (u : Fin N) (y : Tier → ℝ) :
    pair G (Function.update x u y - x) = ∑ i, G u i * (y i - x u i) := by
  unfold pair
  rw [Finset.sum_eq_single u]
  · simp [Function.update_self]
  · intro v _ hv
    simp [Function.update_of_ne hv]
  · intro h
    exact absurd (Finset.mem_univ u) h

lemma pair_add {N : ℕ} (A B z : Fin N → Tier → ℝ) : pair (A + B) z = pair A z + pair B z := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

lemma pair_sub_left {N : ℕ} (A B z : Fin N → Tier → ℝ) :
    pair (A - B) z = pair A z - pair B z := by
  unfold pair
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

lemma pair_price {N : ℕ} (P : Params N) (r : ℝ) (x x' : Fin N → Tier → ℝ) :
    pair (price P r) (x' - x) = r * (load P x' - load P x) := by
  unfold pair load
  have h : ∀ v, ∑ i, price P r v i * (x' - x) v i =
      r * (1 / (P.n : ℝ)) * (P.delta v * x' v .clet - P.delta v * x v .clet) := by
    intro v
    rw [sum_tier, price_m, price_clet, price_cloud]
    simp only [Pi.sub_apply]
    ring
  rw [Finset.sum_congr rfl (fun v _ => h v), ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

lemma pair_price_diff {N : ℕ} (P : Params N) (a b : ℝ) (x x' : Fin N → Tier → ℝ) :
    pair (price P a - price P b) (x' - x) = (a - b) * (load P x' - load P x) := by
  rw [pair_sub_left, pair_price, pair_price]
  ring

lemma pair_self_zero {N : ℕ} (G x : Fin N → Tier → ℝ) : pair G (x - x) = 0 := by
  simp [pair]

lemma pair_comb {N : ℕ} (G a b xb : Fin N → Tier → ℝ) (l : ℝ) :
    pair G (l • a + (1 - l) • b - xb) = l * pair G (a - xb) + (1 - l) * pair G (b - xb) := by
  unfold pair
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma load_comb {N : ℕ} (P : Params N) (a b : Fin N → Tier → ℝ) (l : ℝ) :
    load P (l • a + (1 - l) • b) = l * load P a + (1 - l) * load P b := by
  unfold load
  have h : ∀ v, P.delta v * (l • a + (1 - l) • b) v .clet =
      l * (P.delta v * a v .clet) + (1 - l) * (P.delta v * b v .clet) := by
    intro v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun v _ => h v), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  ring

/-! ### Convexity of the feasible sets -/

lemma Ktil_comb {N : ℕ} {P : Params N} {u : Fin N} {a b : Tier → ℝ}
    (ha : a ∈ Ktil P u) (hb : b ∈ Ktil P u) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    l • a + (1 - l) • b ∈ Ktil P u := by
  simp only [Ktil, Set.mem_setOf_eq] at ha hb ⊢
  obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hb
  have h1' : 0 ≤ 1 - l := by linarith
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩ <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · exact add_nonneg (mul_nonneg h0 (ha0 i)) (mul_nonneg h1' (hb0 i))
  · linear_combination l * ha1 + (1 - l) * hb1
  · nlinarith [mul_le_mul_of_nonneg_left ha2 h0, mul_le_mul_of_nonneg_left hb2 h1']
  · nlinarith [mul_le_mul_of_nonneg_left ha3 h0, mul_le_mul_of_nonneg_left hb3 h1']

lemma Kprod_comb {N : ℕ} {P : Params N} {a b : Fin N → Tier → ℝ}
    (ha : a ∈ Kprod P) (hb : b ∈ Kprod P) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    l • a + (1 - l) • b ∈ Kprod P := by
  rw [mem_Kprod] at ha hb ⊢
  intro v
  have := Ktil_comb (ha v) (hb v) h0 h1
  simpa only [Pi.add_apply, Pi.smul_apply] using this

lemma upd_mem {N : ℕ} {P : Params N} {x : Fin N → Tier → ℝ} (hx : x ∈ Kprod P) {u : Fin N}
    {y : Tier → ℝ} (hy : y ∈ Ktil P u) : Function.update x u y ∈ Kprod P := by
  rw [mem_Kprod] at hx ⊢
  intro v
  by_cases h : v = u
  · subst h
    rw [Function.update_self]
    exact hy
  · rw [Function.update_of_ne h]
    exact hx v

def zc (y : Tier → ℝ) : Tier → ℝ
  | .m => y .m
  | .clet => 0
  | .cloud => y .clet + y .cloud

lemma zc_mem {N : ℕ} {P : Params N} {u : Fin N} {y : Tier → ℝ} (hy : y ∈ Ktil P u) :
    zc y ∈ Ktil P u := by
  simp only [Ktil, Set.mem_setOf_eq] at hy ⊢
  obtain ⟨h0, h1, h2, h3⟩ := hy
  have e0 := h0 .m
  have e1 := h0 .clet
  have e2 := h0 .cloud
  refine ⟨fun i => ?_, ?_, ?_, ?_⟩
  · cases i
    · exact e0
    · exact le_refl (0 : ℝ)
    · show 0 ≤ y .clet + y .cloud
      linarith
  · show y .m + 0 + (y .clet + y .cloud) = 1
    linarith
  · show (0 : ℝ) + (y .clet + y .cloud) ≤ P.chi
    linarith
  · show P.alpha u * P.Pm u * y .m + P.beta u * P.Pt u * (0 + (y .clet + y .cloud)) ≤ P.Pmax u
    rw [zero_add]
    linarith

/-! ### The Lagrange multiplier of the shared constraint -/

lemma key_ineq {N : ℕ} (P : Params N) (G xb : Fin N → Tier → ℝ)
    (hvi : ∀ x ∈ K P, 0 ≤ pair G (x - xb)) {a b : Fin N → Tier → ℝ}
    (ha : a ∈ Kprod P) (hb : b ∈ Kprod P) (h1 : load P a ≤ P.Umax) (h2 : P.Umax ≤ load P b)
    (h3 : load P a < load P b) :
    0 ≤ (load P b - P.Umax) * pair G (a - xb) + (P.Umax - load P a) * pair G (b - xb) := by
  have hpos : 0 < load P b - load P a := by linarith
  have hl0 : 0 ≤ (load P b - P.Umax) / (load P b - load P a) := div_nonneg (by linarith) hpos.le
  have hl1 : (load P b - P.Umax) / (load P b - load P a) ≤ 1 := by
    rw [div_le_one hpos]; linarith
  set l := (load P b - P.Umax) / (load P b - load P a) with hl
  have hlm : l * (load P b - load P a) = load P b - P.Umax := div_mul_cancel₀ _ hpos.ne'
  have hw : l • a + (1 - l) • b ∈ K P := by
    refine ⟨Kprod_comb ha hb hl0 hl1, ?_⟩
    show load P (l • a + (1 - l) • b) ≤ P.Umax
    rw [load_comb]
    nlinarith [hlm]
  have hφ := hvi _ hw
  rw [pair_comb] at hφ
  have e : (load P b - P.Umax) * pair G (a - xb) + (P.Umax - load P a) * pair G (b - xb) =
      (load P b - load P a) * (l * pair G (a - xb) + (1 - l) * pair G (b - xb)) := by
    linear_combination (pair G (b - xb) - pair G (a - xb)) * hlm
  rw [e]
  exact mul_nonneg hpos.le hφ

lemma multiplier {N : ℕ} (P : Params N) (G xb : Fin N → Tier → ℝ) (hxb : xb ∈ K P)
    (hvi : ∀ x ∈ K P, 0 ≤ pair G (x - xb)) (x0 : Fin N → Tier → ℝ) (hx0 : x0 ∈ Kprod P)
    (hl0 : load P x0 < P.Umax) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ * (load P xb - P.Umax) = 0 ∧
      ∀ x ∈ Kprod P, 0 ≤ pair G (x - xb) + ρ * (load P x - load P xb) := by
  have hxbK : xb ∈ Kprod P := hxb.1
  have hxbU : load P xb ≤ P.Umax := hxb.2
  have memK : ∀ x ∈ Kprod P, load P x ≤ P.Umax → x ∈ K P := fun x hx h => ⟨hx, h⟩
  rcases hxbU.lt_or_eq with hlt | heq
  · refine ⟨0, le_rfl, by ring, fun x hx => ?_⟩
    rw [zero_mul, add_zero]
    rcases le_or_gt (load P x) P.Umax with h | h
    · exact hvi x (memK x hx h)
    · have hk := key_ineq P G xb hvi hxbK hx hxbU h.le (by linarith)
      rw [pair_self_zero, mul_zero, zero_add] at hk
      nlinarith [sub_pos.2 hlt]
  · set T : Set ℝ := (fun x => pair G (x - xb) / (P.Umax - load P x)) ''
      {x | x ∈ Kprod P ∧ load P x < P.Umax} with hT
    have hTne : T.Nonempty := ⟨_, x0, ⟨hx0, hl0⟩, rfl⟩
    have hT0 : ∀ t ∈ T, 0 ≤ t := by
      rintro t ⟨x, ⟨hx, hlx⟩, rfl⟩
      exact div_nonneg (hvi x (memK x hx hlx.le)) (by linarith)
    have hTb : BddBelow T := ⟨0, hT0⟩
    refine ⟨sInf T, le_csInf hTne hT0, by rw [heq]; ring, fun x hx => ?_⟩
    rw [heq]
    rcases lt_trichotomy (load P x) P.Umax with h | h | h
    · have hle := csInf_le hTb (show pair G (x - xb) / (P.Umax - load P x) ∈ T from
        ⟨x, ⟨hx, h⟩, rfl⟩)
      rw [le_div_iff₀ (by linarith)] at hle
      nlinarith [hle]
    · rw [h, sub_self, mul_zero, add_zero]
      exact hvi x (memK x hx h.le)
    · have hle : -pair G (x - xb) / (load P x - P.Umax) ≤ sInf T := by
        apply le_csInf hTne
        rintro t ⟨a, ⟨ha, hla⟩, rfl⟩
        have hk := key_ineq P G xb hvi ha hx hla.le h.le (by linarith)
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [hk]
      rw [div_le_iff₀ (by linarith)] at hle
      nlinarith [hle]

/-! ### Positivity facts for one user -/

lemma one_sub_alpha_pos {N : ℕ} (P : Params N) (hA : P.AssumptionA) (u : Fin N) (y : Tier → ℝ)
    (hy : y ∈ Ktil P u) : 0 < 1 - P.alpha u * y .m := by
  obtain ⟨hα0, hα1, -, -⟩ := hA.2.2 u
  simp only [Ktil, Set.mem_setOf_eq] at hy
  obtain ⟨h0, h1, -, -⟩ := hy
  have e1 := h0 .clet
  have e2 := h0 .cloud
  nlinarith [mul_nonneg hα0.le (show 0 ≤ 1 - y .m by linarith)]

lemma n_pos {N : ℕ} (P : Params N) (hS : P.Standing) : (0 : ℝ) < (P.n : ℝ) :=
  Nat.cast_pos.2 hS.1

lemma hB_nonneg {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hL : ∀ x ∈ Kprod P, load P x < 1) (x : Fin N → Tier → ℝ) (hx : x ∈ Kprod P) (u : Fin N) :
    0 ≤ P.delta u * Cc P u x * (P.delta u / (P.n : ℝ)) := by
  obtain ⟨-, -, hδ0, -⟩ := hA.2.2 u
  have ha : 0 ≤ P.delta u / (P.n : ℝ) := div_nonneg hδ0.le (n_pos P hS).le
  have hxu := (mem_Kprod P x).1 hx u
  simp only [Ktil, Set.mem_setOf_eq] at hxu
  have hc0 := hxu.1 .clet
  have hD : 0 < D P x := by unfold D; linarith [hL x hx]
  rw [D_eq P u] at hD
  have hC : 0 ≤ Cc P u x := by nlinarith [mul_nonneg ha hc0]
  exact mul_nonneg (mul_nonneg hδ0.le hC) ha

lemma user_suff {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hL : ∀ x ∈ Kprod P, load P x < 1) (x : Fin N → Tier → ℝ) (hx : x ∈ Kprod P) (u : Fin N)
    (y : Tier → ℝ) (hy : y ∈ Ktil P u) (r : ℝ)
    (hg : 0 ≤ ∑ i, (F P x + price P r) u i * (y i - x u i)) :
    cost P u x + r * (P.delta u / (P.n : ℝ) * x u .clet) ≤
      cost P u (Function.update x u y) + r * (P.delta u / (P.n : ℝ) * y .clet) := by
  rw [Phi_self, Phi_upd]
  rw [grad_eq] at hg
  have hp := one_sub_alpha_pos P hA u (x u) ((mem_Kprod P x).1 hx u)
  have hq := one_sub_alpha_pos P hA u y hy
  have hd0 : 0 < Cc P u x - P.delta u / (P.n : ℝ) * x u .clet := by
    rw [← D_eq]; unfold D; linarith [hL x hx]
  have hd1 : 0 < Cc P u x - P.delta u / (P.n : ℝ) * y .clet := by
    rw [← D_update]; unfold D; linarith [hL _ (upd_mem hx hy)]
  have := scalar_suff (P.alpha u) (P.beta u) (P.gamma u) (P.delta u) (Cc P u x)
    (P.delta u / (P.n : ℝ)) r (x u .m) (x u .clet) (x u .cloud) (y .m) (y .clet) (y .cloud)
    hp hq hd0 hd1 (hB_nonneg P hA hS hL x hx u)
  linarith

lemma user_nec {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hL : ∀ x ∈ Kprod P, load P x < 1) (x : Fin N → Tier → ℝ) (hx : x ∈ Kprod P) (u : Fin N)
    (y : Tier → ℝ) (hy : y ∈ Ktil P u) (r : ℝ)
    (hmin : ∀ z ∈ Ktil P u, cost P u x + r * (P.delta u / (P.n : ℝ) * x u .clet) ≤
      cost P u (Function.update x u z) + r * (P.delta u / (P.n : ℝ) * z .clet)) :
    0 ≤ ∑ i, (F P x + price P r) u i * (y i - x u i) := by
  rw [grad_eq]
  have hxu := (mem_Kprod P x).1 hx u
  have hp := one_sub_alpha_pos P hA u (x u) hxu
  have hq := one_sub_alpha_pos P hA u y hy
  have hd0 : 0 < Cc P u x - P.delta u / (P.n : ℝ) * x u .clet := by
    rw [← D_eq]; unfold D; linarith [hL x hx]
  have hd1 : 0 < Cc P u x - P.delta u / (P.n : ℝ) * y .clet := by
    rw [← D_update]; unfold D; linarith [hL _ (upd_mem hx hy)]
  apply scalar_nec (P.alpha u) (P.beta u) (P.gamma u) (P.delta u) (Cc P u x)
    (P.delta u / (P.n : ℝ)) r (x u .m) (x u .clet) (x u .cloud) (y .m) (y .clet) (y .cloud)
    hp hq hd0 hd1 (hB_nonneg P hA hS hL x hx u)
  intro t ht0 ht1
  have hz := hmin (t • y + (1 - t) • x u) (Ktil_comb hy hxu ht0.le ht1)
  rw [Phi_self, Phi_upd] at hz
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hz

/-! ### The three parts of Theorem 2 -/

lemma vi_to_ne {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hL : ∀ x ∈ Kprod P, load P x < 1) (xb : Fin N → Tier → ℝ)
    (h : IsVISol (K P) (F P) xb) : ∃ ρb, IsExtNE P xb ρb := by
  obtain ⟨hxb, hvi⟩ := h
  have hxbK : xb ∈ Kprod P := hxb.1
  have hU : load P xb ≤ P.Umax := hxb.2
  have hx0 : (fun v => zc (xb v)) ∈ Kprod P :=
    (mem_Kprod P _).2 fun v => zc_mem ((mem_Kprod P xb).1 hxbK v)
  have hl0 : load P (fun v => zc (xb v)) < P.Umax := by
    have e : load P (fun v => zc (xb v)) = 0 := by simp [load, zc]
    rw [e]
    exact hA.1
  obtain ⟨ρ, hρ0, hcomp, hall⟩ := multiplier P (F P xb) xb hxb hvi _ hx0 hl0
  refine ⟨ρ, (mem_Kprod P xb).1 hxbK, hρ0, fun u y hy => ?_, fun ρ' hρ' => ?_⟩
  · apply user_suff P hA hS hL xb hxbK u y hy ρ
    have := hall _ (upd_mem hxbK hy)
    rw [← pair_update (F P xb + price P ρ) xb u y, pair_add, pair_price]
    exact this
  · rw [hcomp]
    nlinarith [mul_nonneg hρ' (sub_nonneg.2 hU)]

lemma ne_to_vi {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hL : ∀ x ∈ Kprod P, load P x < 1) (xb : Fin N → Tier → ℝ) (ρb : ℝ)
    (h : IsExtNE P xb ρb) : IsVISol (K P) (F P) xb := by
  obtain ⟨hK, hρ0, hmin, hρ⟩ := h
  have hU : load P xb ≤ P.Umax := by
    by_contra hc
    push_neg at hc
    have := hρ (ρb + 1) (by linarith)
    nlinarith
  have hcomp : ρb * (load P xb - P.Umax) = 0 := by
    have h0 := hρ 0 le_rfl
    apply le_antisymm
    · nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hU)]
    · linarith
  have hxbK : xb ∈ Kprod P := (mem_Kprod P xb).2 hK
  refine ⟨⟨hxbK, hU⟩, fun x hx => ?_⟩
  have hxK : x ∈ Kprod P := hx.1
  have hxU : load P x ≤ P.Umax := hx.2
  have hsum : 0 ≤ pair (F P xb + price P ρb) (x - xb) := by
    unfold pair
    apply Finset.sum_nonneg
    intro u _
    have := user_nec P hA hS hL xb hxbK u (x u) ((mem_Kprod P x).1 hxK u) ρb (hmin u)
    simpa only [Pi.sub_apply] using this
  rw [pair_add, pair_price] at hsum
  nlinarith [mul_nonneg hρ0 (sub_nonneg.2 hxU)]

lemma mono {N : ℕ} (P : Params N) (h : IsMonotoneOn (Kprod P) (F P)) :
    IsMonotoneOnE (Ke P) (Fe P) := by
  intro p hp q hq
  have e : pairE (Fe P q - Fe P p) (q - p) = pair (F P q.1 - F P p.1) (q.1 - p.1) := by
    simp only [pairE, Fe, Prod.fst_sub, Prod.snd_sub]
    rw [show F P q.1 + price P q.2 - (F P p.1 + price P p.2) =
        (F P q.1 - F P p.1) + (price P q.2 - price P p.2) by abel]
    rw [pair_add, pair_price_diff]
    ring
  rw [e]
  exact h p.1 hp.1 q.1 hq.1

end OffloadT2

open OffloadGNEP.Ext in
theorem solution {N : ℕ} (P : Params N)
    (hA : P.AssumptionA) (hS : P.Standing) :
    ((∀ x ∈ Kprod P, load P x < 1) →
      ∀ xb, IsVISol (K P) (F P) xb ↔ ∃ ρb, IsExtNE P xb ρb) ∧
    (IsMonotoneOn (Kprod P) (F P) → IsMonotoneOnE (Ke P) (Fe P)) := by
  refine ⟨fun hL xb => ⟨fun h => OffloadT2.vi_to_ne P hA hS hL xb h,
    fun ⟨ρb, h⟩ => OffloadT2.ne_to_vi P hA hS hL xb ρb h⟩, OffloadT2.mono P⟩
