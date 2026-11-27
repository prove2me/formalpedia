-- Prove2me | solution 1 for StableSKC.Galois.Supplement.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:19.960236+00:00
-- url     : https://prove2.me/submissions/2b9559c4-4e49-4508-891e-76d88b2e470e

import Mathlib
import Definitions.Def_StableSKC_Galois_Model
import Definitions.Def_RolesForceSeven_sts
import Definitions.Def_StableSKC_Galois_Supplement_NodeLine

open RolesForceSeven

open StableSKC
open StableSKC.Galois
open StableSKC.Galois.Supplement

theorem solution (S : STS 7) (x : Fin 7 ≃ Fin 7) (ℓ : Fin 7 ≃ S.lines)
    (hxℓ : ∀ r : Fin 7, x r ∈ (ℓ r : Finset (Fin 7)))
    (T : Fin 7 → Seeding 3 (Fin 8)) (hT : ∀ r : Fin 7, ArisesFrom S (x r) (ℓ r) (T r)) :
    IsStableSKC T ∧
    ∀ a a' : Fin 8, a ≠ a' → ∀ i : ℕ, 1 ≤ i → i ≤ 3 → meetCount T a a' i = 2 ^ (i - 1) := by
      have dist3 : ∀ a b c : Fin 7, ({a, b, c} : Finset (Fin 7)) ∈ S.lines → a ≠ b ∧ a ≠ c ∧ b ≠ c := by
        intro a b c h
        have h3 := S.card_three _ h
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp at h3
        · have := Finset.card_le_two (a := a) (b := c); omega
        · have := Finset.card_le_two (a := b) (b := a); omega
        · have := Finset.card_le_two (a := a) (b := b); omega
      have inter : ∀ m ∈ S.lines, ∀ m' ∈ S.lines, ∀ a b : Fin 7, a ≠ b → a ∈ m → b ∈ m →
          a ∈ m' → b ∈ m' → m = m' := by
        intro m hm m' hm' a b hab ha hb ha' hb'
        obtain ⟨l, _, hu⟩ := S.pair_unique a b hab
        rw [hu m ⟨hm, ha, hb⟩, hu m' ⟨hm', ha', hb'⟩]
      have third : ∀ z w a b : Fin 7, ({z, a, b} : Finset (Fin 7)) ∈ S.lines →
          ({w, a, b} : Finset (Fin 7)) ∈ S.lines → z = w := by
        intro z w a b h1 h2
        obtain ⟨h1a, h1b, hab⟩ := dist3 _ _ _ h1
        have := inter _ h1 _ h2 a b hab (by simp) (by simp) (by simp) (by simp)
        have hz : z ∈ ({w, a, b} : Finset (Fin 7)) := by rw [← this]; simp
        simp at hz
        rcases hz with h | h | h
        · exact h
        · exact absurd h h1a
        · exact absurd h h1b
      have G : ∀ (x0 : Fin 7) (m : Finset (Fin 7)), m ∈ S.lines → x0 ∈ m → ∀ c d : Fin 8, c ≠ d →
          ({c, d} : Finset (Fin 8)) = nodesToPlayers (m.erase x0) →
          ∃ u v : Fin 7, c = u.succ ∧ d = v.succ ∧ m = {x0, u, v} := by
        intro x0 m hm hx0 c d hcd h
        have hc : c ∈ nodesToPlayers (m.erase x0) := by rw [← h]; simp
        have hd : d ∈ nodesToPlayers (m.erase x0) := by rw [← h]; simp
        simp only [nodesToPlayers, Finset.mem_map, Finset.mem_erase, Fin.coe_succEmb] at hc hd
        obtain ⟨u, ⟨hux, hum⟩, rfl⟩ := hc
        obtain ⟨v, ⟨hvx, hvm⟩, rfl⟩ := hd
        have huv : u ≠ v := fun h => hcd (by rw [h])
        refine ⟨u, v, rfl, rfl, ?_⟩
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> assumption
        · rw [S.card_three _ hm, Finset.card_eq_three.mpr ⟨x0, u, v, Ne.symm hux, Ne.symm hvx, huv, rfl⟩]
      have rot : ∀ {a b c : Fin 7}, ({a, b, c} : Finset (Fin 7)) ∈ S.lines →
          ({b, c, a} : Finset (Fin 7)) ∈ S.lines := by
        intro a b c h
        have : ({b, c, a} : Finset (Fin 7)) = {a, b, c} := by
          ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        rw [this]; exact h
      have thirdm : ∀ z a b : Fin 7, ({z, a, b} : Finset (Fin 7)) ∈ S.lines →
          ∀ m ∈ S.lines, a ∈ m → b ∈ m → z ∈ m := by
        intro z a b h m hm ha hb
        obtain ⟨_, _, hab⟩ := dist3 _ _ _ h
        rw [← inter _ h _ hm a b hab (by simp) (by simp) ha hb]; simp
      have Wpre0 : ∀ y z : Fin 7, (((0 : Fin 8) = 0 ∧ y.succ = z.succ) ∨ (y.succ = 0 ∧ (0 : Fin 8) = z.succ) ∨ ∃ y1 y2 : Fin 7, (0 : Fin 8) = y1.succ ∧ y.succ = y2.succ ∧ ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) → y = z := by
        intro y z h
        rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨y1, y2, h, _, _⟩
        · exact Fin.succ_injective _ h
        · exact absurd h (Fin.succ_ne_zero _)
        · exact absurd h.symm (Fin.succ_ne_zero _)
      have Wpre : ∀ a b z : Fin 7, ((a.succ = 0 ∧ b.succ = z.succ) ∨ (b.succ = 0 ∧ a.succ = z.succ) ∨ ∃ y1 y2 : Fin 7, a.succ = y1.succ ∧ b.succ = y2.succ ∧ ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) → ({z, a, b} : Finset (Fin 7)) ∈ S.lines := by
        intro a b z h
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨y1, y2, h1, h2, h3⟩
        · exact absurd h (Fin.succ_ne_zero _)
        · exact absurd h (Fin.succ_ne_zero _)
        · rw [Fin.succ_injective _ h1, Fin.succ_injective _ h2]; exact h3
      have perm : ∀ {a b c d e f : Fin 7}, ({a, b, c} : Finset (Fin 7)) = {d, e, f} → ({d, e, f} : Finset (Fin 7)) ∈ S.lines → ({a, b, c} : Finset (Fin 7)) ∈ S.lines := by
        intro a b c d e f h h'; rw [h]; exact h'
      have key' : ∀ (x0 : Fin 7) (ℓ0 : Finset (Fin 7)) (T0 : Seeding 3 (Fin 8)), ℓ0 ∈ S.lines → x0 ∈ ℓ0 →
          ArisesFrom S x0 ℓ0 T0 → ∀ p q : Fin 8, p < q → ∀ z : Fin 7, ((T0 p = 0 ∧ T0 q = z.succ) ∨ (T0 q = 0 ∧ T0 p = z.succ) ∨ ∃ y1 y2 : Fin 7, T0 p = y1.succ ∧ T0 q = y2.succ ∧ ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) →
          (((p : ℕ) / 2 = (q : ℕ) / 2 → z = x0) ∧ ((p : ℕ) / 4 = (q : ℕ) / 4 → (p : ℕ) / 2 ≠ (q : ℕ) / 2 → z ∈ ℓ0 ∧ z ≠ x0) ∧
            ((p : ℕ) / 4 ≠ (q : ℕ) / 4 → z ∉ ℓ0)) := by
        intro x0 ℓ0 T0 hℓ0 hx0 hA
        obtain ⟨h0, h1, h23, h47⟩ := hA
        replace h1 : T0 1 = x0.succ := h1
        obtain ⟨u1, v1, h2, h3, hL1⟩ := G x0 ℓ0 hℓ0 hx0 (T0 2) (T0 3) (T0.injective.ne (by decide)) h23
        have hm45 : ({T0 4, T0 5} : Finset (Fin 8)) ∈ (S.lines.filter fun m => x0 ∈ m ∧ m ≠ ℓ0).image fun m => nodesToPlayers (m.erase x0) := by rw [← h47]; simp
        have hm67 : ({T0 6, T0 7} : Finset (Fin 8)) ∈ (S.lines.filter fun m => x0 ∈ m ∧ m ≠ ℓ0).image fun m => nodesToPlayers (m.erase x0) := by rw [← h47]; simp
        simp only [Finset.mem_image, Finset.mem_filter] at hm45 hm67
        obtain ⟨m2, ⟨hm2, hxm2, _⟩, hm2e⟩ := hm45
        obtain ⟨m3, ⟨hm3, hxm3, _⟩, hm3e⟩ := hm67
        obtain ⟨u2, v2, h4, h5, hL2⟩ := G x0 m2 hm2 hxm2 (T0 4) (T0 5) (T0.injective.ne (by decide)) hm2e.symm
        obtain ⟨u3, v3, h6, h7, hL3⟩ := G x0 m3 hm3 hxm3 (T0 6) (T0 7) (T0.injective.ne (by decide)) hm3e.symm
        subst hL1 hL2 hL3
        clear hm2e hm3e h23 h47 hx0
        have d01 : x0 ≠ u1 := by intro h; rw [h] at h1; exact absurd (T0.injective (h1.trans h2.symm)) (by decide)
        have e01 : u1 ≠ x0 := Ne.symm d01
        have d02 : x0 ≠ v1 := by intro h; rw [h] at h1; exact absurd (T0.injective (h1.trans h3.symm)) (by decide)
        have e02 : v1 ≠ x0 := Ne.symm d02
        have d03 : x0 ≠ u2 := by intro h; rw [h] at h1; exact absurd (T0.injective (h1.trans h4.symm)) (by decide)
        have e03 : u2 ≠ x0 := Ne.symm d03
        have d04 : x0 ≠ v2 := by intro h; rw [h] at h1; exact absurd (T0.injective (h1.trans h5.symm)) (by decide)
        have e04 : v2 ≠ x0 := Ne.symm d04
        have d05 : x0 ≠ u3 := by intro h; rw [h] at h1; exact absurd (T0.injective (h1.trans h6.symm)) (by decide)
        have e05 : u3 ≠ x0 := Ne.symm d05
        have d06 : x0 ≠ v3 := by intro h; rw [h] at h1; exact absurd (T0.injective (h1.trans h7.symm)) (by decide)
        have e06 : v3 ≠ x0 := Ne.symm d06
        have d12 : u1 ≠ v1 := by intro h; rw [h] at h2; exact absurd (T0.injective (h2.trans h3.symm)) (by decide)
        have e12 : v1 ≠ u1 := Ne.symm d12
        have d13 : u1 ≠ u2 := by intro h; rw [h] at h2; exact absurd (T0.injective (h2.trans h4.symm)) (by decide)
        have e13 : u2 ≠ u1 := Ne.symm d13
        have d14 : u1 ≠ v2 := by intro h; rw [h] at h2; exact absurd (T0.injective (h2.trans h5.symm)) (by decide)
        have e14 : v2 ≠ u1 := Ne.symm d14
        have d15 : u1 ≠ u3 := by intro h; rw [h] at h2; exact absurd (T0.injective (h2.trans h6.symm)) (by decide)
        have e15 : u3 ≠ u1 := Ne.symm d15
        have d16 : u1 ≠ v3 := by intro h; rw [h] at h2; exact absurd (T0.injective (h2.trans h7.symm)) (by decide)
        have e16 : v3 ≠ u1 := Ne.symm d16
        have d23 : v1 ≠ u2 := by intro h; rw [h] at h3; exact absurd (T0.injective (h3.trans h4.symm)) (by decide)
        have e23 : u2 ≠ v1 := Ne.symm d23
        have d24 : v1 ≠ v2 := by intro h; rw [h] at h3; exact absurd (T0.injective (h3.trans h5.symm)) (by decide)
        have e24 : v2 ≠ v1 := Ne.symm d24
        have d25 : v1 ≠ u3 := by intro h; rw [h] at h3; exact absurd (T0.injective (h3.trans h6.symm)) (by decide)
        have e25 : u3 ≠ v1 := Ne.symm d25
        have d26 : v1 ≠ v3 := by intro h; rw [h] at h3; exact absurd (T0.injective (h3.trans h7.symm)) (by decide)
        have e26 : v3 ≠ v1 := Ne.symm d26
        have d34 : u2 ≠ v2 := by intro h; rw [h] at h4; exact absurd (T0.injective (h4.trans h5.symm)) (by decide)
        have e34 : v2 ≠ u2 := Ne.symm d34
        have d35 : u2 ≠ u3 := by intro h; rw [h] at h4; exact absurd (T0.injective (h4.trans h6.symm)) (by decide)
        have e35 : u3 ≠ u2 := Ne.symm d35
        have d36 : u2 ≠ v3 := by intro h; rw [h] at h4; exact absurd (T0.injective (h4.trans h7.symm)) (by decide)
        have e36 : v3 ≠ u2 := Ne.symm d36
        have d45 : v2 ≠ u3 := by intro h; rw [h] at h5; exact absurd (T0.injective (h5.trans h6.symm)) (by decide)
        have e45 : u3 ≠ v2 := Ne.symm d45
        have d46 : v2 ≠ v3 := by intro h; rw [h] at h5; exact absurd (T0.injective (h5.trans h7.symm)) (by decide)
        have e46 : v3 ≠ v2 := Ne.symm d46
        have d56 : u3 ≠ v3 := by intro h; rw [h] at h6; exact absurd (T0.injective (h6.trans h7.symm)) (by decide)
        have e56 : v3 ≠ u3 := Ne.symm d56
        have cov : ∀ w : Fin 7, w = x0 ∨ w = u1 ∨ w = v1 ∨ w = u2 ∨ w = v2 ∨ w = u3 ∨ w = v3 := by
          intro w
          obtain ⟨s, hs⟩ := T0.surjective w.succ
          rcases (by decide : ∀ s : Fin 8, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7) s with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
          all_goals simp only [h0, h1, h2, h3, h4, h5, h6, h7] at hs
          · exact absurd hs.symm (Fin.succ_ne_zero _)
          · left; exact (Fin.succ_injective _ hs).symm
          · right; left; exact (Fin.succ_injective _ hs).symm
          · right; right; left; exact (Fin.succ_injective _ hs).symm
          · right; right; right; left; exact (Fin.succ_injective _ hs).symm
          · right; right; right; right; left; exact (Fin.succ_injective _ hs).symm
          · right; right; right; right; right; left; exact (Fin.succ_injective _ hs).symm
          · right; right; right; right; right; right; exact (Fin.succ_injective _ hs).symm
        intro p q hpq z hW
        rcases (by decide : ∀ s : Fin 8, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7) p with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals rcases (by decide : ∀ s : Fin 8, s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7) q with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        · exact absurd hpq (by decide)
        · refine ⟨fun _ => ?_, fun hc hc' => absurd hc' (by decide), fun hc => absurd hc (by decide)⟩
          rw [h0, h1] at hW
          have hW := Wpre0 _ _ hW; subst hW
          rfl
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h0, h2] at hW
          have hW := Wpre0 _ _ hW; subst hW
          simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h0, h3] at hW
          have hW := Wpre0 _ _ hW; subst hW
          simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h0, h4] at hW
          have hW := Wpre0 _ _ hW; subst hW
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨by assumption, by assumption, by assumption⟩
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h0, h5] at hW
          have hW := Wpre0 _ _ hW; subst hW
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨by assumption, by assumption, by assumption⟩
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h0, h6] at hW
          have hW := Wpre0 _ _ hW; subst hW
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨by assumption, by assumption, by assumption⟩
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h0, h7] at hW
          have hW := Wpre0 _ _ hW; subst hW
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨by assumption, by assumption, by assumption⟩
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h1, h2] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · exact absurd rfl (dist3 _ _ _ hW).1
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h1, h3] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · exact absurd rfl (dist3 _ _ _ hW).1
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h1, h4] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h1, h5] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h1, h6] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h1, h7] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · refine ⟨fun _ => ?_, fun hc hc' => absurd hc' (by decide), fun hc => absurd hc (by decide)⟩
          rw [h2, h3] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · rfl
          · exact absurd rfl (dist3 _ _ _ hW).1
          · exact absurd rfl (dist3 _ _ _ hW).2.1
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h2, h4] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h2, h5] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h2, h6] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h2, h7] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h3, h4] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h3, h5] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h3, h6] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
        · refine ⟨fun hc => absurd hc (by decide), fun hc _ => absurd hc (by decide), fun _ => ?_⟩
          rw [h3, h7] at hW
          have hW := Wpre _ _ _ hW
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl|rfl|rfl)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hℓ0 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · refine ⟨fun _ => ?_, fun hc hc' => absurd hc' (by decide), fun hc => absurd hc (by decide)⟩
          rw [h4, h5] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · rfl
          · have hh := thirdm _ _ _ hW _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · exact absurd rfl (dist3 _ _ _ hW).2.1
          · have hh := thirdm _ _ _ hW _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h4, h6] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).2.1
          · have hh := thirdm _ _ _ (rot hW) _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h4, h7] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ (rot hW) _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).2.1
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h5, h6] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · exact absurd rfl (dist3 _ _ _ hW).2.1
          · have hh := thirdm _ _ _ (rot hW) _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
        · refine ⟨fun hc => absurd hc (by decide), fun _ _ => ?_, fun hc => absurd hc (by decide)⟩
          rw [h5, h7] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton]; exact ⟨by simp, by assumption⟩
          · have hh := thirdm _ _ _ (rot (rot hW)) _ hm2 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · have hh := thirdm _ _ _ (rot hW) _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).2.1
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · refine ⟨fun _ => ?_, fun hc hc' => absurd hc' (by decide), fun hc => absurd hc (by decide)⟩
          rw [h6, h7] at hW
          have hW := Wpre _ _ _ hW
          rcases cov z with rfl|rfl|rfl|rfl|rfl|rfl|rfl
          · rfl
          · have hh := thirdm _ _ _ hW _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · have hh := thirdm _ _ _ hW _ hm3 (by simp) (by simp); simp only [Finset.mem_insert, Finset.mem_singleton] at hh; rcases hh with h | h | h <;> exact absurd h (by assumption)
          · exact absurd rfl (dist3 _ _ _ hW).1
          · exact absurd rfl (dist3 _ _ _ hW).2.1
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)
        · exact absurd hpq (by decide)

      have key : ∀ (x0 : Fin 7) (ℓ0 : Finset (Fin 7)) (T0 : Seeding 3 (Fin 8)), ℓ0 ∈ S.lines → x0 ∈ ℓ0 →
          ArisesFrom S x0 ℓ0 T0 → ∀ p q : Fin 8, p ≠ q → ∀ z : Fin 7,
          ((T0 p = 0 ∧ T0 q = z.succ) ∨ (T0 q = 0 ∧ T0 p = z.succ) ∨
            ∃ y1 y2 : Fin 7, T0 p = y1.succ ∧ T0 q = y2.succ ∧ ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) →
          (((p : ℕ) / 2 = (q : ℕ) / 2 → z = x0) ∧ ((p : ℕ) / 4 = (q : ℕ) / 4 → (p : ℕ) / 2 ≠ (q : ℕ) / 2 → z ∈ ℓ0 ∧ z ≠ x0) ∧
            ((p : ℕ) / 4 ≠ (q : ℕ) / 4 → z ∉ ℓ0)) := by
        intro x0 ℓ0 T0 h1 h2 h3 p q hpq z hW
        rcases lt_or_gt_of_ne hpq with h | h
        · exact key' x0 ℓ0 T0 h1 h2 h3 p q h z hW
        · have hW' : ((T0 q = 0 ∧ T0 p = z.succ) ∨ (T0 p = 0 ∧ T0 q = z.succ) ∨
              ∃ y1 y2 : Fin 7, T0 q = y1.succ ∧ T0 p = y2.succ ∧ ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) := by
            rcases hW with ⟨a, b⟩ | ⟨a, b⟩ | ⟨y1, y2, a, b, c⟩
            · exact Or.inr (Or.inl ⟨a, b⟩)
            · exact Or.inl ⟨a, b⟩
            · exact Or.inr (Or.inr ⟨y2, y1, b, a, by rw [Finset.pair_comm]; exact c⟩)
          obtain ⟨c1, c2, c3⟩ := key' x0 ℓ0 T0 h1 h2 h3 q p h z hW'
          exact ⟨fun e => c1 e.symm, fun e e' => c2 e.symm (Ne.symm e'), fun e => c3 (Ne.symm e)⟩
      have exW : ∀ a a' : Fin 8, a ≠ a' → ∃ z : Fin 7, ((a = 0 ∧ a' = z.succ) ∨ (a' = 0 ∧ a = z.succ) ∨
            ∃ y1 y2 : Fin 7, a = y1.succ ∧ a' = y2.succ ∧ ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) := by
        intro a a' h
        cases a using Fin.cases with
        | zero =>
          cases a' using Fin.cases with
          | zero => exact absurd rfl h
          | succ y => exact ⟨y, Or.inl ⟨rfl, rfl⟩⟩
        | succ y1 =>
          cases a' using Fin.cases with
          | zero => exact ⟨y1, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          | succ y2 =>
            have hne : y1 ≠ y2 := fun e => h (by rw [e])
            obtain ⟨m, ⟨hm, h1, h2⟩, _⟩ := S.pair_unique y1 y2 hne
            have hc : ((m.erase y1).erase y2).card = 1 := by
              rw [Finset.card_erase_of_mem (by simp [h2, Ne.symm hne]), Finset.card_erase_of_mem h1,
                S.card_three _ hm]
            obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
            have hzm : z ∈ (m.erase y1).erase y2 := by rw [hz]; simp
            simp only [Finset.mem_erase] at hzm
            obtain ⟨hz2, hz1, hzm⟩ := hzm
            refine ⟨z, Or.inr (Or.inr ⟨y1, y2, rfl, rfl, ?_⟩)⟩
            have : ({z, y1, y2} : Finset (Fin 7)) = m := by
              apply Finset.eq_of_subset_of_card_le
              · intro w hw; simp at hw; rcases hw with rfl | rfl | rfl <;> assumption
              · rw [S.card_three _ hm, Finset.card_eq_three.mpr ⟨z, y1, y2, hz1, hz2, hne, rfl⟩]
            rw [this]; exact hm
      have rounds : ∀ r : Fin 7, ∀ a a' : Fin 8, a ≠ a' → ∀ z : Fin 7,
          ((a = 0 ∧ a' = z.succ) ∨ (a' = 0 ∧ a = z.succ) ∨
            ∃ y1 y2 : Fin 7, a = y1.succ ∧ a' = y2.succ ∧ ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) →
          (CanMeetIn (T r) a a' 1 ↔ z = x r) ∧
          (CanMeetIn (T r) a a' 2 ↔ z ∈ (ℓ r : Finset (Fin 7)) ∧ z ≠ x r) ∧
          (CanMeetIn (T r) a a' 3 ↔ z ∉ (ℓ r : Finset (Fin 7))) := by
        intro r a a' haa z hW
        have hW' : (((T r) ((T r).symm a) = 0 ∧ (T r) ((T r).symm a') = z.succ) ∨
            ((T r) ((T r).symm a') = 0 ∧ (T r) ((T r).symm a) = z.succ) ∨
            ∃ y1 y2 : Fin 7, (T r) ((T r).symm a) = y1.succ ∧ (T r) ((T r).symm a') = y2.succ ∧
              ({z, y1, y2} : Finset (Fin 7)) ∈ S.lines) := by
          simp only [Equiv.apply_symm_apply]; exact hW
        have hpq : (T r).symm a ≠ (T r).symm a' := fun e => haa ((T r).symm.injective e)
        obtain ⟨c1, c2, c3⟩ := key (x r) (ℓ r) (T r) (ℓ r).2 (hxℓ r) (hT r) _ _ hpq z hW'
        have hv : ((T r).symm a : ℕ) ≠ ((T r).symm a' : ℕ) := fun e => hpq (Fin.ext e)
        have hp8 : ((T r).symm a : ℕ) < 8 := ((T r).symm a).2
        have hq8 : ((T r).symm a' : ℕ) < 8 := ((T r).symm a').2
        have e1 : CanMeetIn (T r) a a' 1 ↔ ((T r).symm a : ℕ) / 2 = ((T r).symm a' : ℕ) / 2 := by
          unfold CanMeetIn; norm_num; omega
        have e2 : CanMeetIn (T r) a a' 2 ↔ ((T r).symm a : ℕ) / 4 = ((T r).symm a' : ℕ) / 4 ∧
            ((T r).symm a : ℕ) / 2 ≠ ((T r).symm a' : ℕ) / 2 := by
          unfold CanMeetIn; norm_num
        have e3 : CanMeetIn (T r) a a' 3 ↔ ((T r).symm a : ℕ) / 4 ≠ ((T r).symm a' : ℕ) / 4 := by
          unfold CanMeetIn; norm_num; omega
        have hx := hxℓ r
        rw [e1, e2, e3]
        refine ⟨⟨c1, fun hz => ?_⟩, ⟨fun h => c2 h.1 h.2, fun hz => ?_⟩, ⟨c3, fun hz => ?_⟩⟩
        · by_contra h
          by_cases h4 : ((T r).symm a : ℕ) / 4 = ((T r).symm a' : ℕ) / 4
          · exact (c2 h4 h).2 hz
          · exact c3 h4 (hz ▸ hx)
        · by_cases h2 : ((T r).symm a : ℕ) / 2 = ((T r).symm a' : ℕ) / 2
          · exact absurd (c1 h2) hz.2
          · by_cases h4 : ((T r).symm a : ℕ) / 4 = ((T r).symm a' : ℕ) / 4
            · exact ⟨h4, h2⟩
            · exact absurd hz.1 (c3 h4)
        · intro h4
          by_cases h2 : ((T r).symm a : ℕ) / 2 = ((T r).symm a' : ℕ) / 2
          · exact hz (c1 h2 ▸ hx)
          · exact hz (c2 h4 h2).1
      have cnt : ∀ z : Fin 7, (Finset.univ.filter fun r => z ∈ (ℓ r : Finset (Fin 7))).card = 3 := by
        intro z
        have hA := hT (x.symm z)
        have hxz : x (x.symm z) = z := x.apply_symm_apply z
        rw [hxz] at hA
        have hzl := hxℓ (x.symm z)
        rw [hxz] at hzl
        obtain ⟨_, _, _, h47⟩ := hA
        have hinj : Set.InjOn (fun m : Finset (Fin 7) => nodesToPlayers (m.erase z))
            ↑(S.lines.filter fun m => z ∈ m ∧ m ≠ (ℓ (x.symm z) : Finset (Fin 7))) := by
          intro m hm m' hm' e
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hm hm'
          have : m.erase z = m'.erase z := Finset.map_injective _ e
          rw [← Finset.insert_erase hm.2.1, ← Finset.insert_erase hm'.2.1, this]
        have hc2 : (S.lines.filter fun m => z ∈ m ∧ m ≠ (ℓ (x.symm z) : Finset (Fin 7))).card = 2 := by
          rw [← Finset.card_image_of_injOn hinj, ← h47]
          apply Finset.card_pair
          intro e
          have : T (x.symm z) 4 ∈ ({T (x.symm z) 6, T (x.symm z) 7} : Finset (Fin 8)) := by rw [← e]; simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h <;> exact absurd ((T (x.symm z)).injective h) (by decide)
        have hsplit : S.lines.filter (fun m => z ∈ m) = insert (ℓ (x.symm z) : Finset (Fin 7))
            (S.lines.filter fun m => z ∈ m ∧ m ≠ (ℓ (x.symm z) : Finset (Fin 7))) := by
          ext m
          simp only [Finset.mem_filter, Finset.mem_insert]
          by_cases hm : m = (ℓ (x.symm z) : Finset (Fin 7))
          · subst hm; simp [(ℓ (x.symm z)).2, hzl]
          · simp [hm]
        have h3 : (S.lines.filter fun m => z ∈ m).card = 3 := by
          rw [hsplit, Finset.card_insert_of_notMem (by simp), hc2]
        rw [← h3]
        apply Finset.card_bij (fun r _ => (ℓ r : Finset (Fin 7)))
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
          exact ⟨(ℓ r).2, hr⟩
        · intro r1 _ r2 _ e; exact ℓ.injective (Subtype.ext e)
        · intro m hm
          simp only [Finset.mem_filter] at hm
          exact ⟨ℓ.symm ⟨m, hm.1⟩, by simp [hm.2], by simp⟩
      have main : ∀ a a' : Fin 8, a ≠ a' → ∀ i : ℕ, 1 ≤ i → i ≤ 3 → meetCount T a a' i = 2 ^ (i - 1) := by
        intro a a' h i hi1 hi3
        obtain ⟨z, hW⟩ := exW a a' h
        have hI := fun r => rounds r a a' h z hW
        have hx1 : (Finset.univ.filter fun r => z = x r).card = 1 := by
          rw [Finset.card_eq_one]
          refine ⟨x.symm z, ?_⟩
          ext r
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro rfl; simp
          · rintro rfl; simp
        interval_cases i
        · unfold meetCount
          rw [Finset.filter_congr (fun r _ => (hI r).1)]
          simpa using hx1
        · unfold meetCount
          rw [Finset.filter_congr (fun r _ => (hI r).2.1)]
          have hsum := Finset.card_filter_add_card_filter_not
            (s := Finset.univ.filter fun r => z ∈ (ℓ r : Finset (Fin 7))) (fun r => z = x r)
          rw [Finset.filter_filter, Finset.filter_filter, cnt z] at hsum
          have hb : (Finset.univ.filter fun r => z ∈ (ℓ r : Finset (Fin 7)) ∧ z = x r).card = 1 := by
            rw [← hx1]
            congr 1
            apply Finset.filter_congr
            intro r _
            constructor
            · exact fun h => h.2
            · intro h; exact ⟨h ▸ hxℓ r, h⟩
          norm_num
          omega
        · unfold meetCount
          rw [Finset.filter_congr (fun r _ => (hI r).2.2)]
          have hsum := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin 7))) (fun r => z ∈ (ℓ r : Finset (Fin 7)))
          rw [cnt z] at hsum
          simp only [Finset.card_univ, Fintype.card_fin] at hsum
          norm_num
          omega
      exact ⟨⟨by simp, fun i h1 h3 => ⟨2 ^ (i - 1), fun a a' h => main a a' h i h1 h3⟩⟩, main⟩
