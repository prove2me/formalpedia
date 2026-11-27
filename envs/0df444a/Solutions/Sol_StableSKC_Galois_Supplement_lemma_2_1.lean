-- Prove2me | solution 1 for StableSKC.Galois.Supplement.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:36.211161+00:00
-- url     : https://prove2.me/submissions/82e41c52-1d9d-4d72-a8ef-08aa7c6b6422

import Mathlib
import Definitions.Def_StableSKC_Galois_Model
import Definitions.Def_RolesForceSeven_sts
import Definitions.Def_StableSKC_Galois_Supplement_NodeLine

open RolesForceSeven

open StableSKC
open StableSKC.Galois
open StableSKC.Galois.Supplement

theorem solution (S : STS 7) (x : Fin 7) (ℓ : Finset (Fin 7)) (hℓ : ℓ ∈ S.lines) (hx : x ∈ ℓ)
    (T : Seeding 3 (Fin 8)) (hT : ArisesFrom S x ℓ T) :
    (∀ y : Fin 7,
      (CanMeetIn T 0 (nodePlayer y) 1 ↔ y = x) ∧
      (CanMeetIn T 0 (nodePlayer y) 2 ↔ y ∈ ℓ ∧ y ≠ x) ∧
      (CanMeetIn T 0 (nodePlayer y) 3 ↔ y ∉ ℓ)) ∧
    (∀ y x₁ x₂ : Fin 7, ({y, x₁, x₂} : Finset (Fin 7)) ∈ S.lines → ∀ i : ℕ,
      (CanMeetIn T (nodePlayer x₁) (nodePlayer x₂) i ↔ CanMeetIn T 0 (nodePlayer y) i)) := by
        set_option maxRecDepth 3000 in
          classical
          rcases hT with ⟨h0, h1, h23, h4567⟩
          let p : Fin 7 → ℕ := fun y => (T.symm (nodePlayer y)).val
          have hpbound (y : Fin 7) : p y < 8 := (T.symm (nodePlayer y)).isLt
          have hp0 : T.symm 0 = 0 := by apply T.injective; simpa using h0.symm
          have hpx : p x = 1 := by
            have : T.symm (nodePlayer x) = 1 := by apply T.injective; simpa using h1.symm
            simp [p, this]
          have hpinj : Function.Injective p := by
            intro a b hab
            apply Fin.succ_injective
            apply T.symm.injective
            exact Fin.ext hab
          have hpne0 (y : Fin 7) : p y ≠ 0 := by
            intro hy
            have : T.symm (nodePlayer y) = T.symm 0 := by rw [hp0]; exact Fin.ext hy
            have := T.symm.injective this
            simp [nodePlayer] at this
          have hpeq (y : Fin 7) : p y = 1 ↔ y = x := by
            constructor
            · intro hy; apply hpinj; omega
            · rintro rfl; exact hpx
          have hmem (m : Finset (Fin 7)) (y : Fin 7) :
              nodePlayer y ∈ nodesToPlayers m ↔ y ∈ m := by
            simp [nodesToPlayers, nodePlayer]
          have hpos (y : Fin 7) (j : Fin 8) : nodePlayer y = T j ↔ p y = j.val := by
            constructor
            · intro h; simp [p, h]
            · intro h
              have he : T.symm (nodePlayer y) = j := Fin.ext h
              simpa using congrArg T he
          have hlinepos (y : Fin 7) : y ∈ ℓ ∧ y ≠ x ↔ p y = 2 ∨ p y = 3 := by
            have hh := hmem (ℓ.erase x) y
            rw [← h23] at hh
            simpa [Finset.mem_erase, hpos, and_comm] using hh.symm
          have hfirst : ∀ y : Fin 7,
              (CanMeetIn T 0 (nodePlayer y) 1 ↔ y = x) ∧
              (CanMeetIn T 0 (nodePlayer y) 2 ↔ y ∈ ℓ ∧ y ≠ x) ∧
              (CanMeetIn T 0 (nodePlayer y) 3 ↔ y ∉ ℓ) := by
            intro y
            have hb := hpbound y
            have hn := hpne0 y
            have he := hpeq y
            have hl := hlinepos y
            have hxmem : y = x → y ∈ ℓ := by rintro rfl; exact hx
            simp only [CanMeetIn, hp0]
            change (_ ↔ y = x) ∧ (_ ↔ y ∈ ℓ ∧ y ≠ x) ∧ (_ ↔ y ∉ ℓ)
            norm_num
            change (0 = p y / 2 ∧ 0 ≠ p y ↔ y = x) ∧
              (0 = p y / 4 ∧ 0 ≠ p y / 2 ↔ y ∈ ℓ ∧ y ≠ x) ∧
              (0 = p y / 8 ∧ 0 ≠ p y / 4 ↔ y ∉ ℓ)
            have hly : y ∈ ℓ ↔ p y = 1 ∨ p y = 2 ∨ p y = 3 := by
              constructor
              · intro hy
                by_cases hyx : y = x
                · exact Or.inl (he.mpr hyx)
                · exact Or.inr (hl.mp ⟨hy, hyx⟩)
              · rintro (hy | hy)
                · exact hxmem (he.mp hy)
                · exact (hl.mpr hy).1
            refine ⟨?_, ?_, ?_⟩
            · rw [← he]; omega
            · rw [hl]; omega
            · rw [hly]; omega
          have hshape (m : Finset (Fin 7)) (hm : m ∈ S.lines) (hxm : x ∈ m) :
              nodesToPlayers (m.erase x) = {T 2, T 3} ∨
              nodesToPlayers (m.erase x) = {T 4, T 5} ∨
              nodesToPlayers (m.erase x) = {T 6, T 7} := by
            by_cases he : m = ℓ
            · subst m
              exact Or.inl h23.symm
            · have hh : nodesToPlayers (m.erase x) ∈
                  (S.lines.filter fun m => x ∈ m ∧ m ≠ ℓ).image
                    (fun m => nodesToPlayers (m.erase x)) := by
                exact Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, hxm, he⟩, rfl⟩
              rw [← h4567] at hh
              exact Or.inr (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hh)
          have hquarter (m : Finset (Fin 7)) (hm : m ∈ S.lines) (hxm : x ∈ m)
              (a b : Fin 7) (ha : a ∈ m) (hb : b ∈ m) (hax : a ≠ x) (hbx : b ≠ x) :
              p a / 2 = p b / 2 := by
            have ha' : nodePlayer a ∈ nodesToPlayers (m.erase x) :=
              (hmem _ _).mpr (Finset.mem_erase.mpr ⟨hax, ha⟩)
            have hb' : nodePlayer b ∈ nodesToPlayers (m.erase x) :=
              (hmem _ _).mpr (Finset.mem_erase.mpr ⟨hbx, hb⟩)
            rcases hshape m hm hxm with hh | hh | hh <;>
              rw [hh] at ha' hb' <;>
              simp only [Finset.mem_insert, Finset.mem_singleton, hpos] at ha' hb' <;>
              norm_num at ha' hb' <;> omega
          have hpairlines (q : Finset (Fin 8))
              (hq : q = {T 2, T 3} ∨ q = {T 4, T 5} ∨ q = {T 6, T 7}) :
              ∃ m ∈ S.lines, x ∈ m ∧ nodesToPlayers (m.erase x) = q := by
            rcases hq with rfl | hq
            · exact ⟨ℓ, hℓ, hx, h23.symm⟩
            · have hq' : q ∈ ({{T 4, T 5}, {T 6, T 7}} : Finset (Finset (Fin 8))) := by
                simpa only [Finset.mem_insert, Finset.mem_singleton] using hq
              rw [h4567] at hq'
              obtain ⟨m, hm, he⟩ := Finset.mem_image.mp hq'
              obtain ⟨hm, hxm, _⟩ := Finset.mem_filter.mp hm
              exact ⟨m, hm, hxm, he⟩
          have hcover (a b : Fin 7) (hab : a ≠ b) (hq : p a / 2 = p b / 2) :
              ∃ m ∈ S.lines, x ∈ m ∧ a ∈ m ∧ b ∈ m := by
            have ha0 := hpne0 a
            have hb0 := hpne0 b
            have ha8 := hpbound a
            have hb8 := hpbound b
            have habp : p a ≠ p b := fun h => hab (hpinj h)
            have hc : ((p a = 2 ∨ p a = 3) ∧ (p b = 2 ∨ p b = 3)) ∨
                ((p a = 4 ∨ p a = 5) ∧ (p b = 4 ∨ p b = 5)) ∨
                ((p a = 6 ∨ p a = 7) ∧ (p b = 6 ∨ p b = 7)) := by omega
            have haux (j k : Fin 8)
                (hj : ({T j, T k} : Finset (Fin 8)) = {T 2, T 3} ∨
                  ({T j, T k} : Finset (Fin 8)) = {T 4, T 5} ∨
                  ({T j, T k} : Finset (Fin 8)) = {T 6, T 7})
                (ha : p a = j.val ∨ p a = k.val) (hb : p b = j.val ∨ p b = k.val) :
                ∃ m ∈ S.lines, x ∈ m ∧ a ∈ m ∧ b ∈ m := by
              obtain ⟨m, hm, hxm, he⟩ := hpairlines {T j, T k} hj
              have ha' : nodePlayer a ∈ nodesToPlayers (m.erase x) := by
                rw [he]
                simpa only [Finset.mem_insert, Finset.mem_singleton, hpos] using ha
              have hb' : nodePlayer b ∈ nodesToPlayers (m.erase x) := by
                rw [he]
                simpa only [Finset.mem_insert, Finset.mem_singleton, hpos] using hb
              exact ⟨m, hm, hxm, (Finset.mem_erase.mp ((hmem _ _).mp ha')).2,
                (Finset.mem_erase.mp ((hmem _ _).mp hb')).2⟩
            rcases hc with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact haux 2 3 (Or.inl rfl) ha hb
            · exact haux 4 5 (Or.inr (Or.inl rfl)) ha hb
            · exact haux 6 7 (Or.inr (Or.inr rfl)) ha hb
          have hdistinct (y a b : Fin 7) (hm : ({y, a, b} : Finset (Fin 7)) ∈ S.lines) :
              y ≠ a ∧ y ≠ b ∧ a ≠ b := by
            have hc := S.card_three _ hm
            have hya : y ≠ a := by
              intro he
              have hh : ({y, a, b} : Finset (Fin 7)) = {a, b} := by simp [he]
              rw [hh] at hc
              have hle : ({a, b} : Finset (Fin 7)).card ≤ 2 := Finset.card_le_two
              omega
            have hyb : y ≠ b := by
              intro he
              have hh : ({y, a, b} : Finset (Fin 7)) = {a, b} := by simp [he]
              rw [hh] at hc
              have hle : ({a, b} : Finset (Fin 7)).card ≤ 2 := Finset.card_le_two
              omega
            have hab : a ≠ b := by
              intro he
              have hh : ({y, a, b} : Finset (Fin 7)) = {y, b} := by simp [he]
              rw [hh] at hc
              have hle : ({y, b} : Finset (Fin 7)).card ≤ 2 := Finset.card_le_two
              omega
            exact ⟨hya, hyb, hab⟩
          have hthird (y a b : Fin 7) (hm : ({y, a, b} : Finset (Fin 7)) ∈ S.lines) :
              p a / 2 = p b / 2 ↔ y = x := by
            obtain ⟨hya, hyb, hab⟩ := hdistinct y a b hm
            constructor
            · intro hq
              obtain ⟨m, hm', hxm, ham, hbm⟩ := hcover a b hab hq
              obtain ⟨m₀, _, hu⟩ := S.pair_unique a b hab
              have he : m = ({y, a, b} : Finset (Fin 7)) :=
                (hu m ⟨hm', ham, hbm⟩).trans (hu _ ⟨hm, by simp, by simp⟩).symm
              rw [he] at hxm
              have ha0 := hpne0 a
              have hb0 := hpne0 b
              have habp : p a ≠ p b := fun h => hab (hpinj h)
              have hax : a ≠ x := by
                intro hh
                have hpax : p a = 1 := by simpa [hh] using hpx
                omega
              have hbx : b ≠ x := by
                intro hh
                have hpbx : p b = 1 := by simpa [hh] using hpx
                omega
              have hxy : x = y := by
                simpa only [Finset.mem_insert, Finset.mem_singleton,
                  Ne.symm hax, Ne.symm hbx, or_false] using hxm
              exact hxy.symm
            · intro hyx
              exact hquarter {y, a, b} hm (by simp [← hyx]) a b
                (by simp) (by simp) (by simpa [← hyx] using hya.symm)
                (by simpa [← hyx] using hyb.symm)
          refine ⟨hfirst, ?_⟩
          intro y a b hm i
          obtain ⟨hya, hyb, hab⟩ := hdistinct y a b hm
          have hpa := hpbound a
          have hpb := hpbound b
          have hpy := hpbound y
          have hna := hpne0 a
          have hnb := hpne0 b
          have hny := hpne0 y
          have hpay : p y ≠ p a := fun h => hya (hpinj h)
          have hpby : p y ≠ p b := fun h => hyb (hpinj h)
          have hpab : p a ≠ p b := fun h => hab (hpinj h)
          have hqab : p a / 2 = p b / 2 ↔ p y = 1 :=
            (hthird y a b hm).trans (hpeq y).symm
          have hqyb : p y / 2 = p b / 2 ↔ p a = 1 := by
            exact (hthird a y b (by simpa [Finset.insert_comm] using hm)).trans (hpeq a).symm
          have hqya : p y / 2 = p a / 2 ↔ p b = 1 := by
            have he : ({b, y, a} : Finset (Fin 7)) = {y, a, b} := by
              ext z
              simp only [Finset.mem_insert, Finset.mem_singleton]
              tauto
            exact (hthird b y a (by rw [he]; exact hm)).trans (hpeq b).symm
          simp only [CanMeetIn, hp0]
          change (1 ≤ i ∧ i ≤ 3 ∧ p a / 2 ^ i = p b / 2 ^ i ∧
              p a / 2 ^ (i - 1) ≠ p b / 2 ^ (i - 1)) ↔
            (1 ≤ i ∧ i ≤ 3 ∧ 0 / 2 ^ i = p y / 2 ^ i ∧
              0 / 2 ^ (i - 1) ≠ p y / 2 ^ (i - 1))
          by_cases hi : 1 ≤ i ∧ i ≤ 3
          · obtain ⟨hi1, hi3⟩ := hi
            interval_cases i <;> norm_num <;> omega
          · tauto
