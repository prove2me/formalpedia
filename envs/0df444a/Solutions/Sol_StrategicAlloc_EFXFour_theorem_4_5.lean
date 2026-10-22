-- Prove2me | solution 1 for StrategicAlloc.EFXFour.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T19:09:30.738478+00:00
-- url     : https://prove2.me/submissions/4bc22c39-db1a-4c3b-903e-a4733aaba2c7

import Mathlib
import Definitions.Def_StrategicAlloc_EFXFour_Setting

set_option autoImplicit false

namespace P45

lemma fin2_cases (i j k : Fin 2) (h : i ≠ j) : k = i ∨ k = j := by
  revert i j k; decide

lemma alloc_compl (A : Fin 2 → Finset (Fin 4))
    (hA : StrategicAlloc.RRFair.IsAllocation A) (i j : Fin 2) (hij : i ≠ j) :
    A j = (A i)ᶜ := by
  ext g
  rw [Finset.mem_compl]
  constructor
  · intro hg hgi
    exact Finset.disjoint_left.mp (hA.1 hij) hgi hg
  · intro hgi
    have : g ∈ Finset.univ.biUnion A := by rw [hA.2]; exact Finset.mem_univ g
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.mp this
    rcases fin2_cases i j k hij with rfl | rfl
    · exact absurd hk hgi
    · exact hk

lemma upd_bid (b : Fin 2 → Fin 4 → ℝ) (hb0 : ∀ k g, 0 ≤ b k g) (i : Fin 2)
    (bs : Fin 4 → ℝ) (hbs : ∀ g, 0 ≤ bs g) : ∀ k g, 0 ≤ Function.update b i bs k g := by
  intro k g
  by_cases hk : k = i
  · subst hk; simp [hbs]
  · rw [Function.update_of_ne hk]; exact hb0 k g

lemma exists_best (M : StrategicAlloc.EFXFour.Mechanism 4) (b : Fin 2 → Fin 4 → ℝ)
    (hb0 : ∀ k g, 0 ≤ b k g) (i : Fin 2) (w : Fin 4 → ℝ) :
    ∃ bs : Fin 4 → ℝ, (∀ g, 0 ≤ bs g) ∧ ∀ b' : Fin 4 → ℝ, (∀ g, 0 ≤ b' g) →
      ∑ g ∈ M (Function.update b i b') i, w g ≤ ∑ g ∈ M (Function.update b i bs) i, w g := by
  classical
  let Sf : Finset (Finset (Fin 4)) := Finset.univ.filter
    (fun T => ∃ b' : Fin 4 → ℝ, (∀ g, 0 ≤ b' g) ∧ M (Function.update b i b') i = T)
  have hne : Sf.Nonempty := ⟨M b i, by
    simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨b i, hb0 i, by rw [Function.update_eq_self]⟩⟩
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image Sf (fun T => ∑ g ∈ T, w g) hne
  simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and] at hT
  obtain ⟨bs, hbs, rfl⟩ := hT
  refine ⟨bs, hbs, fun b' hb' => hmax _ ?_⟩
  simp only [Sf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨b', hb', rfl⟩

lemma efx_of_best (M : StrategicAlloc.EFXFour.Mechanism 4)
    (hM : StrategicAlloc.EFXFour.IsAlwaysEFXMechanism M) (b : Fin 2 → Fin 4 → ℝ)
    (hb0 : ∀ k g, 0 ≤ b k g) (i : Fin 2) (w : Fin 4 → ℝ) (hw : ∀ g, 0 ≤ w g)
    (bs : Fin 4 → ℝ) (hbs : ∀ g, 0 ≤ bs g)
    (hbest : ∀ b' : Fin 4 → ℝ, (∀ g, 0 ≤ b' g) →
      ∑ g ∈ M (Function.update b i b') i, w g ≤ ∑ g ∈ M (Function.update b i bs) i, w g) :
    ∀ j, (M (Function.update b i bs) j).Nonempty → ∀ g ∈ M (Function.update b i bs) j, 0 < w g →
      ∑ h ∈ (M (Function.update b i bs) j).erase g, w h ≤
        ∑ h ∈ M (Function.update b i bs) i, w h := by
  classical
  let v' : Fin 2 → Fin 4 → ℝ := fun k => if k = i then w else 0
  have hv' : ∀ k g, 0 ≤ v' k g := by
    intro k g; by_cases hk : k = i <;> simp [v', hk, hw]
  have hpne : StrategicAlloc.RRFair.IsPNE M v' (Function.update b i bs) := by
    refine ⟨upd_bid b hb0 i bs hbs, ?_⟩
    intro k b' hb'
    by_cases hk : k = i
    · subst hk
      simpa [StrategicAlloc.RRFair.val, v', Function.update_idem] using hbest b' hb'
    · simp [StrategicAlloc.RRFair.val, v', hk]
  have hefx := (hM.2 v' hv').2 _ hpne
  intro j hj g hg hpos
  have := hefx i j hj g hg (by simp [v', hpos])
  simpa [StrategicAlloc.RRFair.val, v'] using this

lemma sum_univ_ite (S : Finset (Fin 4)) (f : Fin 4 → ℝ) :
    ∑ g ∈ S, f g = ∑ g, if g ∈ S then f g else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_lab (h1 h2 h3 h4 : Fin 4)
    (hcov : ∀ g, g = h1 ∨ g = h2 ∨ g = h3 ∨ g = h4)
    (d12 : h1 ≠ h2) (d13 : h1 ≠ h3) (d14 : h1 ≠ h4) (d23 : h2 ≠ h3) (d24 : h2 ≠ h4)
    (d34 : h3 ≠ h4) (S : Finset (Fin 4)) (f : Fin 4 → ℝ) :
    ∑ g ∈ S, f g = (if h1 ∈ S then f h1 else 0) + (if h2 ∈ S then f h2 else 0) +
      (if h3 ∈ S then f h3 else 0) + (if h4 ∈ S then f h4 else 0) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {h1, h2, h3, h4} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hcov g
  rw [sum_univ_ite S f, huniv, Finset.sum_insert (by simp [d12, d13, d14]),
    Finset.sum_insert (by simp [d23, d24]), Finset.sum_insert (by simp [d34]),
    Finset.sum_singleton]
  ring

/-- The `v∗` step of the paper's proof (p. 20): with `u = (1.2, 1, 1, 0.1)` on
`h1, h2, h3, h4`, every bundle `T` that is EFX (w.r.t. `u`) for its holder beats `{h3, h4}`
under `a`, given `a h3 < a h1`, `a h4 < a h1`, `a h4 < a h2`. -/
lemma stepB (a u : Fin 4 → ℝ) (h1 h2 h3 h4 : Fin 4)
    (hcov : ∀ g, g = h1 ∨ g = h2 ∨ g = h3 ∨ g = h4)
    (d12 : h1 ≠ h2) (d13 : h1 ≠ h3) (d14 : h1 ≠ h4) (d23 : h2 ≠ h3) (d24 : h2 ≠ h4)
    (d34 : h3 ≠ h4) (ha : ∀ g, 0 ≤ a g)
    (hu1 : u h1 = 6 / 5) (hu2 : u h2 = 1) (hu3 : u h3 = 1) (hu4 : u h4 = 1 / 10)
    (o1 : a h3 < a h1) (o2 : a h4 < a h1) (o3 : a h4 < a h2) (T : Finset (Fin 4))
    (hT : ∀ g ∉ T, 0 < u g → ∑ x ∈ Tᶜ.erase g, u x ≤ ∑ x ∈ T, u x) :
    a h3 + a h4 < ∑ x ∈ T, a x := by
  have L := sum_lab h1 h2 h3 h4 hcov d12 d13 d14 d23 d24 d34
  have e1 := hT h1
  have e2 := hT h2
  have e3 := hT h3
  have e4 := hT h4
  rw [L T a]
  rw [L T u, L (Tᶜ.erase h1) u] at e1
  rw [L T u, L (Tᶜ.erase h2) u] at e2
  rw [L T u, L (Tᶜ.erase h3) u] at e3
  rw [L T u, L (Tᶜ.erase h4) u] at e4
  simp only [Finset.mem_erase, Finset.mem_compl, ne_eq, d12, d13, d14, d23, d24, d34,
    Ne.symm d12, Ne.symm d13, Ne.symm d14, Ne.symm d23, Ne.symm d24, Ne.symm d34,
    not_true_eq_false, not_false_eq_true, true_and, false_and, hu1, hu2, hu3, hu4]
    at e1 e2 e3 e4
  have := ha h1
  have := ha h2
  have := ha h3
  have := ha h4
  by_cases m1 : h1 ∈ T <;> by_cases m2 : h2 ∈ T <;> by_cases m3 : h3 ∈ T <;>
    by_cases m4 : h4 ∈ T <;>
    simp only [m1, m2, m3, m4, if_true, if_false, not_true_eq_false, not_false_eq_true,
      true_implies, false_implies] at e1 e2 e3 e4 ⊢ <;>
    (try norm_num at e1) <;> (try norm_num at e2) <;> (try norm_num at e3) <;>
    (try norm_num at e4) <;> (try norm_num) <;> linarith

/-- The combinatorial heart of Theorem 4.5. -/
lemma core (a : Fin 4 → ℝ) (ha : ∀ g, 0 ≤ a g) (P B : Finset (Fin 4))
    (hE : ∀ g ∉ P, 0 < a g → ∑ x ∈ Pᶜ.erase g, a x ≤ ∑ x ∈ P, a x)
    (hB1 : ∑ x ∈ P, a x < ∑ x ∈ B, a x) (hB2 : ∑ x ∈ P, a x < ∑ x ∈ Bᶜ, a x)
    (hK : ∀ u : Fin 4 → ℝ, (∀ g, 0 ≤ u g) → ∃ T : Finset (Fin 4),
      (∀ g ∉ T, 0 < u g → ∑ x ∈ Tᶜ.erase g, u x ≤ ∑ x ∈ T, u x) ∧
      ∑ x ∈ T, a x ≤ ∑ x ∈ P, a x) : False := by
  classical
  have hnn : ∀ S : Finset (Fin 4), 0 ≤ ∑ x ∈ S, a x :=
    fun S => Finset.sum_nonneg (fun g _ => ha g)
  set Z := P.filter (fun x => x ∈ B) with hZ
  set Y := P.filter (fun x => ¬ x ∈ B) with hY
  set W := Pᶜ.filter (fun x => x ∈ B) with hW
  set X := Pᶜ.filter (fun x => ¬ x ∈ B) with hX
  have sP : ∑ x ∈ P, a x = ∑ x ∈ Z, a x + ∑ x ∈ Y, a x :=
    (Finset.sum_filter_add_sum_filter_not P (fun x => x ∈ B) a).symm
  have sPc : ∑ x ∈ Pᶜ, a x = ∑ x ∈ W, a x + ∑ x ∈ X, a x :=
    (Finset.sum_filter_add_sum_filter_not Pᶜ (fun x => x ∈ B) a).symm
  have sB : ∑ x ∈ B, a x = ∑ x ∈ Z, a x + ∑ x ∈ W, a x := by
    rw [← Finset.sum_filter_add_sum_filter_not B (fun x => x ∈ P) a]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext g; simp only [hZ, Finset.mem_filter]; tauto
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext g; simp only [hW, Finset.mem_filter, Finset.mem_compl]; tauto
  have sBc : ∑ x ∈ Bᶜ, a x = ∑ x ∈ Y, a x + ∑ x ∈ X, a x := by
    rw [← Finset.sum_filter_add_sum_filter_not Bᶜ (fun x => x ∈ P) a]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext g; simp only [hY, Finset.mem_filter, Finset.mem_compl]; tauto
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext g; simp only [hX, Finset.mem_filter, Finset.mem_compl]; tauto
  have hYW : ∑ x ∈ Y, a x < ∑ x ∈ W, a x := by linarith
  have hZX : ∑ x ∈ Z, a x < ∑ x ∈ X, a x := by linarith
  obtain ⟨w0, hw0W, hw0pos⟩ : ∃ w ∈ W, 0 < a w := by
    by_contra h
    push Not at h
    have := Finset.sum_nonpos h
    linarith [hnn Y]
  obtain ⟨x0, hx0X, hx0pos⟩ : ∃ x ∈ X, 0 < a x := by
    by_contra h
    push Not at h
    have := Finset.sum_nonpos h
    linarith [hnn Z]
  have hw0P : w0 ∈ Pᶜ := (Finset.mem_filter.mp hw0W).1
  have hx0P : x0 ∈ Pᶜ := (Finset.mem_filter.mp hx0X).1
  have ew := hE w0 (Finset.mem_compl.mp hw0P) hw0pos
  have ex := hE x0 (Finset.mem_compl.mp hx0P) hx0pos
  have ew' := Finset.sum_erase_add Pᶜ a hw0P
  have ex' := Finset.sum_erase_add Pᶜ a hx0P
  have lw : a w0 ≤ ∑ x ∈ W, a x := Finset.single_le_sum (fun g _ => ha g) hw0W
  have lx : a x0 ≤ ∑ x ∈ X, a x := Finset.single_le_sum (fun g _ => ha g) hx0X
  have hYpos : 0 < ∑ x ∈ Y, a x := by linarith
  have hZpos : 0 < ∑ x ∈ Z, a x := by linarith
  have ne_of_pos : ∀ S : Finset (Fin 4), 0 < ∑ x ∈ S, a x → S.Nonempty := by
    intro S hS
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty] at hS; exact absurd hS (lt_irrefl 0)
    · exact h
  have cZ := Finset.card_pos.mpr (ne_of_pos Z hZpos)
  have cY := Finset.card_pos.mpr (ne_of_pos Y hYpos)
  have cW := Finset.card_pos.mpr ⟨w0, hw0W⟩
  have cX := Finset.card_pos.mpr ⟨x0, hx0X⟩
  have cP := Finset.card_filter_add_card_filter_not (s := P) (fun x => x ∈ B)
  have cPc := Finset.card_filter_add_card_filter_not (s := Pᶜ) (fun x => x ∈ B)
  have cc : P.card + Pᶜ.card = 4 := by
    rw [Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_univ P
    rw [Fintype.card_fin] at this
    omega
  rw [← hZ, ← hY] at cP
  rw [← hW, ← hX] at cPc
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (show Z.card = 1 by omega)
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (show Y.card = 1 by omega)
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (show W.card = 1 by omega)
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (show X.card = 1 by omega)
  have mz : z ∈ P ∧ z ∈ B := by
    have : z ∈ Z := by rw [hz]; exact Finset.mem_singleton_self z
    exact Finset.mem_filter.mp this
  have my : y ∈ P ∧ ¬ y ∈ B := by
    have : y ∈ Y := by rw [hy]; exact Finset.mem_singleton_self y
    exact Finset.mem_filter.mp this
  have mw : w ∈ Pᶜ ∧ w ∈ B := by
    have : w ∈ W := by rw [hw]; exact Finset.mem_singleton_self w
    exact Finset.mem_filter.mp this
  have mx : x ∈ Pᶜ ∧ ¬ x ∈ B := by
    have : x ∈ X := by rw [hx]; exact Finset.mem_singleton_self x
    exact Finset.mem_filter.mp this
  rw [Finset.mem_compl] at mw mx
  have hcov : ∀ g, g = z ∨ g = y ∨ g = w ∨ g = x := by
    intro g
    by_cases gP : g ∈ P <;> by_cases gB : g ∈ B
    · left
      have : g ∈ Z := Finset.mem_filter.mpr ⟨gP, gB⟩
      rw [hz] at this; exact Finset.mem_singleton.mp this
    · right; left
      have : g ∈ Y := Finset.mem_filter.mpr ⟨gP, gB⟩
      rw [hy] at this; exact Finset.mem_singleton.mp this
    · right; right; left
      have : g ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr gP, gB⟩
      rw [hw] at this; exact Finset.mem_singleton.mp this
    · right; right; right
      have : g ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr gP, gB⟩
      rw [hx] at this; exact Finset.mem_singleton.mp this
  have dzy : z ≠ y := by rintro rfl; exact my.2 mz.2
  have dzw : z ≠ w := by rintro rfl; exact mw.1 mz.1
  have dzx : z ≠ x := by rintro rfl; exact mx.1 mz.1
  have dyw : y ≠ w := by rintro rfl; exact mw.1 my.1
  have dyx : y ≠ x := by rintro rfl; exact mx.1 my.1
  have dwx : w ≠ x := by rintro rfl; exact mx.2 mw.2
  rw [hz, Finset.sum_singleton] at sP sB hZX
  rw [hy, Finset.sum_singleton] at sP sBc hYW
  rw [hw, Finset.sum_singleton] at hYW
  rw [hx, Finset.sum_singleton] at hZX
  -- now: P = {z, y}, a y < a w, a z < a x
  let mk : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun p q r g =>
    if g = p then 6 / 5 else if g = q then 1 else if g = r then 1 else 1 / 10
  have mk_nn : ∀ p q r g, 0 ≤ mk p q r g := by
    intro p q r g; simp only [mk]; split_ifs <;> norm_num
  by_cases hcase : a z < a w
  · -- labels (w, x, y, z)
    obtain ⟨T, hT, hTle⟩ := hK (mk w x y) (mk_nn w x y)
    have := stepB a (mk w x y) w x y z (fun g => by rcases hcov g with h | h | h | h <;> tauto)
      dwx (Ne.symm dyw) (Ne.symm dzw) (Ne.symm dyx) (Ne.symm dzx) (Ne.symm dzy) ha
      (by simp [mk]) (by simp [mk, Ne.symm dwx]) (by simp [mk, dyw, dyx])
      (by simp [mk, dzw, dzx, dzy]) hYW hcase hZX T hT
    linarith
  · -- labels (x, w, z, y)
    push Not at hcase
    obtain ⟨T, hT, hTle⟩ := hK (mk x w z) (mk_nn x w z)
    have := stepB a (mk x w z) x w z y (fun g => by rcases hcov g with h | h | h | h <;> tauto)
      (Ne.symm dwx) (Ne.symm dzx) (Ne.symm dyx) (Ne.symm dzw) (Ne.symm dyw) dzy ha
      (by simp [mk]) (by simp [mk, dwx]) (by simp [mk, dzx, dzw])
      (by simp [mk, dyx, dyw, Ne.symm dzy]) hZX (by linarith) hYW T hT
    linarith

end P45

open StrategicAlloc.EFXFour in
theorem solution (M : Mechanism 4) (hM : IsAlwaysEFXMechanism M)
    (v : Fin 2 → Fin 4 → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin 2 → Fin 4 → ℝ) (hb : StrategicAlloc.RRFair.IsPNE M v b) :
    IsApproxMMS 1 v (M b) := by
  classical
  intro i
  by_contra hlt
  push Not at hlt
  rw [one_mul] at hlt
  have hb0 : ∀ k g, 0 ≤ b k g := hb.1
  have hij : i ≠ i + 1 := (by decide : ∀ k : Fin 2, k ≠ k + 1) i
  set j := i + 1 with hj
  have hcomp := P45.alloc_compl (M b) (hM.1 b hb0) i j hij
  have hEFX := (hM.2 v hv).2 b hb
  -- the MMS partition beating agent i's bundle
  unfold mu LittleCharity.MMS.mms at hlt
  obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup hlt
  have h0 := lt_of_lt_of_le hf (ciInf_le (Set.finite_range _).bddBelow 0)
  have h1 := lt_of_lt_of_le hf (ciInf_le (Set.finite_range _).bddBelow 1)
  simp only [StrategicAlloc.RRFair.val] at h0 h1
  let B : Finset (Fin 4) := Finset.univ.filter (fun g => f g = 0)
  have hB1 : ∑ x ∈ M b i, v i x < ∑ x ∈ B, v i x := by
    refine lt_of_lt_of_eq h0 (Finset.sum_congr ?_ (fun _ _ => rfl))
    ext g; simp [B]
  have hB2 : ∑ x ∈ M b i, v i x < ∑ x ∈ Bᶜ, v i x := by
    refine lt_of_lt_of_eq h1 (Finset.sum_congr ?_ (fun _ _ => rfl))
    ext g
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    generalize f g = c
    revert c; decide
  have hE : ∀ g ∉ M b i, 0 < v i g →
      ∑ x ∈ (M b i)ᶜ.erase g, v i x ≤ ∑ x ∈ M b i, v i x := by
    intro g hg hpos
    have hgj : g ∈ M b j := by rw [hcomp]; exact Finset.mem_compl.mpr hg
    have := hEFX i j ⟨g, hgj⟩ g hgj hpos
    simp only [StrategicAlloc.RRFair.val] at this
    rwa [hcomp] at this
  have hK : ∀ u : Fin 4 → ℝ, (∀ g, 0 ≤ u g) → ∃ T : Finset (Fin 4),
      (∀ g ∉ T, 0 < u g → ∑ x ∈ Tᶜ.erase g, u x ≤ ∑ x ∈ T, u x) ∧
      ∑ x ∈ T, v i x ≤ ∑ x ∈ M b i, v i x := by
    intro u hu
    obtain ⟨bs, hbs, hbest⟩ := P45.exists_best M b hb0 i u
    have hefx := P45.efx_of_best M hM b hb0 i u hu bs hbs hbest
    have hc := P45.alloc_compl _ (hM.1 _ (P45.upd_bid b hb0 i bs hbs)) i j hij
    refine ⟨M (Function.update b i bs) i, ?_, ?_⟩
    · intro g hg hpos
      have hgj : g ∈ M (Function.update b i bs) j := by
        rw [hc]; exact Finset.mem_compl.mpr hg
      have := hefx j ⟨g, hgj⟩ g hgj hpos
      rwa [hc] at this
    · exact hb.2 i bs hbs
  exact P45.core (v i) (hv i) (M b i) B hE hB1 hB2 hK
