-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P05.oneBasisClusterCardProductBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:50:52.717605+00:00
-- url     : https://prove2.me/submissions/51ce011e-fe0d-4519-9349-4729da6c2d97

import Mathlib
import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
noncomputable section
open scoped Matrix ComplexOrder
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
open QAlgorithms.Papers.Independent.Independent1.P05
open QAlgorithms
open PresentedCSS

/-- Hamming ball volume. -/
def s199o_V (n r : ℕ) : ℕ :=
  (Finset.univ.filter fun e : Fin n → ZMod 2 => hammingNorm e ≤ r).card

lemma s199o_prod_eq {n : ℕ} (l : ℝ) (e : Fin n → ZMod 2) :
    (∏ i, (if e i = 0 then (1:ℝ) else l)) = l ^ hammingNorm e := by
  rw [Finset.prod_ite]
  simp [Finset.prod_const, hammingNorm]

lemma s199o_ball (n r : ℕ) (l : ℝ) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    (s199o_V n r : ℝ) * l ^ r ≤ (1 + l) ^ n := by
  have h1 : (1 + l) ^ n = ∏ _i : Fin n, ∑ b : ZMod 2, (if b = 0 then (1:ℝ) else l) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    show 1 + l = ∑ b : Fin 2, (if (b : ZMod 2) = 0 then (1:ℝ) else l)
    rw [Fin.sum_univ_two]
    simp
  rw [h1, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  simp_rw [s199o_prod_eq]
  unfold s199o_V
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  calc ∑ x ∈ Finset.univ.filter (fun e : Fin n → ZMod 2 => hammingNorm e ≤ r), ((1:ℕ):ℝ) * l ^ r
      ≤ ∑ x ∈ Finset.univ.filter (fun e : Fin n → ZMod 2 => hammingNorm e ≤ r), l ^ hammingNorm x := by
        apply Finset.sum_le_sum
        intro x hx
        simp only [Finset.mem_filter] at hx
        simp only [Nat.cast_one, one_mul]
        exact pow_le_pow_of_le_one hl0.le hl1 hx.2
    _ ≤ ∑ x : Fin n → ZMod 2, l ^ hammingNorm x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => pow_nonneg hl0.le _)

lemma s199o_V_zero (n : ℕ) : s199o_V n 0 ≤ 1 := by
  unfold s199o_V
  calc _ ≤ ({0} : Finset (Fin n → ZMod 2)).card := by
        apply Finset.card_le_card
        intro e he
        simp only [Finset.mem_filter, Nat.le_zero, hammingNorm_eq_zero] at he
        simp [he.2]
    _ = 1 := Finset.card_singleton _

lemma s199o_four_le (a : ℕ) (ha : 4 ≤ a) : 4 * a ≤ 2 ^ a := by
  induction a, ha using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    have : 4 ≤ 2 ^ k := le_trans (by norm_num) (le_trans (by omega : 16 ≤ 4 * k) ih)
    omega

lemma s199o_vol (n m r : ℕ) (hnpos : 0 < n) (hm : m ≤ n) (hr : 16 * n * r ≤ m ^ 2) :
    (s199o_V n r : ℝ) ^ 2 ≤ 2 ^ m := by
  rcases Nat.eq_zero_or_pos r with h0 | hrpos
  · subst h0
    have := s199o_V_zero n
    have h' : (s199o_V n 0 : ℝ) ≤ 1 := by exact_mod_cast this
    have : (s199o_V n 0 : ℝ) ^ 2 ≤ 1 := by
      have h0' : (0:ℝ) ≤ s199o_V n 0 := Nat.cast_nonneg _
      nlinarith
    exact le_trans this (one_le_pow₀ (by norm_num))
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hr; rcases hr with h | h <;> omega
    · exact h
  have hex : ∃ a, 8 * n ≤ m * 2 ^ a := ⟨n + 3, by
    have : n < 2 ^ n := Nat.lt_two_pow_self
    rw [pow_add]; nlinarith⟩
  set a := Nat.find hex with ha_def
  have ha : 8 * n ≤ m * 2 ^ a := Nat.find_spec hex
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha; omega
  have hlt : m * 2 ^ a < 16 * n := by
    have := Nat.find_min hex (show a - 1 < a by omega)
    push Not at this
    have e : 2 ^ a = 2 * 2 ^ (a - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [e]; nlinarith
  have ham : a * m ≤ 4 * n := by
    rcases le_or_gt a 4 with h | h
    · nlinarith
    · have := s199o_four_le a h.le
      nlinarith
  have har : 4 * a * r ≤ m := by
    have h1 : 16 * n * r * a ≤ m ^ 2 * a := Nat.mul_le_mul_right _ hr
    have h2 : m ^ 2 * a ≤ 4 * n * m := by nlinarith
    have : n * (4 * a * r) ≤ n * m := by nlinarith
    exact Nat.le_of_mul_le_mul_left this hnpos
  -- real part
  set l : ℝ := 1 / 2 ^ a with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by
    rw [hl, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hb := s199o_ball n r l hl0 hl1
  have hlr : l ^ r * (2:ℝ) ^ (a * r) = 1 := by
    rw [hl, div_pow, pow_mul, one_pow]; field_simp
  have hV : (s199o_V n r : ℝ) ≤ (1 + l) ^ n * 2 ^ (a * r) := by
    have : (s199o_V n r : ℝ) = (s199o_V n r : ℝ) * l ^ r * 2 ^ (a * r) := by
      rw [mul_assoc, hlr, mul_one]
    rw [this]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  have hexp : (1 + l) ^ n ≤ Real.exp (n * l) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp l]) n
  have hnl : (n:ℝ) * l ≤ m / 8 := by
    have : (8 * n : ℝ) ≤ m * 2 ^ a := by exact_mod_cast ha
    rw [hl, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith [show (0:ℝ) < 2 ^ a by positivity]
  have h2pow : ∀ j : ℕ, (2:ℝ) ^ j = Real.exp (j * Real.log 2) := by
    intro j
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have har' : (4 * (a * r) : ℝ) ≤ m := by
    have : ((4 * a * r : ℕ) : ℝ) ≤ m := by exact_mod_cast har
    push_cast at this; linarith
  have hlog := Real.log_two_gt_d9
  calc (s199o_V n r : ℝ) ^ 2 ≤ ((1 + l) ^ n * 2 ^ (a * r)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hV 2
    _ ≤ (Real.exp (n * l) * 2 ^ (a * r)) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = Real.exp (2 * (n * l) + 2 * ((a * r : ℕ) * Real.log 2)) := by
        rw [h2pow, ← Real.exp_add, ← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ Real.exp (m * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
    _ = 2 ^ m := (h2pow m).symm

lemma s199o_dual_finrank {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Module.finrank (ZMod 2) C + Module.finrank (ZMod 2) (codeDual C) = n := by
  set e := dotProductEquiv (ZMod 2) (Fin n)
  have heq : codeDual C = C.dualAnnihilator.map e.symm.toLinearMap := by
    ext y
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_dualAnnihilator]
    show (∀ c ∈ C, c ⬝ᵥ y = 0) ↔ _
    simp only [e, dotProductEquiv_apply_apply]
    constructor
    · intro h c hc; rw [dotProduct_comm]; exact h c hc
    · intro h c hc; rw [dotProduct_comm]; exact h c hc
  rw [heq, LinearEquiv.finrank_map_eq, Subspace.finrank_add_finrank_dualAnnihilator_eq,
    Module.finrank_fin_fun]

lemma s199o_card_sub {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := S), ZMod.card]

lemma s199o_dims {n mx mz : ℕ} (C : CheckPresentation n mx mz) :
    Module.finrank (ZMod 2) (codeDual C.Cx) + Module.finrank (ZMod 2) (codeDual C.Cz)
      + C.logicalDimension = n := by
  have h1 := s199o_dual_finrank C.Cx
  have h2 := s199o_dual_finrank C.Cz
  have h3 := Submodule.finrank_quotient_add_finrank ((codeDual C.Cz).comap C.Cx.subtype)
  have h4 := (Submodule.comapSubtypeEquivOfLe C.css).finrank_eq
  have h5 : C.logicalDimension = Module.finrank (ZMod 2)
      (C.Cx ⧸ (codeDual C.Cz).comap C.Cx.subtype) := rfl
  have h6 : Module.finrank (ZMod 2) ((codeDual C.Cz).comap C.Cx.subtype) =
      Module.finrank (ZMod 2) (codeDual C.Cz) := h4
  have h7 : Module.finrank (ZMod 2) C.Cx ≤ n := by omega
  omega

lemma s199o_char2 {n : ℕ} (x s y : Fin n → ZMod 2) : x + s + (x + y + s) = y := by
  ext i
  simp only [Pi.add_apply]
  generalize x i = a; generalize s i = b; generalize y i = c
  revert a b c; decide

lemma s199o_class {n mx mz : ℕ} (C : CheckPresentation n mx mz) (c1 eps1 : ℝ) (had : Bool)
    (B : Finset (NLTSWord n)) (hB : B ∈ nltsClasses C c1 eps1 had) :
    B.card ≤ Fintype.card (nltsOppositeDual C had) * s199o_V n ⌊2*c1*eps1*n⌋₊ := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hB
  set S := nltsOppositeDual C had
  set r := ⌊2*c1*eps1*n⌋₊
  set ball := (Finset.univ.filter fun e : Fin n → ZMod 2 => hammingNorm e ≤ r)
  have hsub : nltsClass C c1 eps1 had x ⊆
      ((Finset.univ : Finset S) ×ˢ ball).image (fun p => x + (p.1 : Fin n → ZMod 2) + p.2) := by
    intro y hy
    simp only [nltsClass, Finset.mem_filter] at hy
    have hrel := hy.2
    unfold nltsRelated NLTS.reducedHammingWeight at hrel
    obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr ⟨(0 : S)⟩)
      (fun s : S => hammingNorm (x + y + (s : Fin n → ZMod 2)))
    rw [hs] at hrel
    rw [Finset.mem_image]
    refine ⟨(s, x + y + (s : Fin n → ZMod 2)), ?_, s199o_char2 _ _ _⟩
    simp only [Finset.mem_product, Finset.mem_univ, true_and, ball, Finset.mem_filter]
    exact Nat.le_floor hrel
  calc (nltsClass C c1 eps1 had x).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset S) ×ˢ ball).card := Finset.card_image_le
    _ = _ := by rw [Finset.card_product, Finset.card_univ]; rfl

theorem solution {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (hn : 0 < n) (hk : 1 ≤ C.logicalDimension) (c1 eps1 : ℝ)
    (hc1 : 0 < c1) (heps : 0 ≤ eps1)
    (hcutoff : 2*c1*eps1 ≤ (((C.logicalDimension : ℝ)-1)/(4*n))^2)
    (Bz : Finset (NLTSWord n)) (hz : Bz ∈ nltsClasses C c1 eps1 false)
    (Bx : Finset (NLTSWord n)) (hx : Bx ∈ nltsClasses C c1 eps1 true) :
    (Bz.card : ℝ)*Bx.card/(2 : ℝ)^n ≤ 1/2 := by
  set k := C.logicalDimension with hkdef
  set r := ⌊2*c1*eps1*n⌋₊
  have hBz := s199o_class C c1 eps1 false Bz hz
  have hBx := s199o_class C c1 eps1 true Bx hx
  have hSz : Fintype.card (nltsOppositeDual C false) =
      2 ^ Module.finrank (ZMod 2) (codeDual C.Cx) := s199o_card_sub _
  have hSx : Fintype.card (nltsOppositeDual C true) =
      2 ^ Module.finrank (ZMod 2) (codeDual C.Cz) := s199o_card_sub _
  have hdims := s199o_dims C
  set a := Module.finrank (ZMod 2) (codeDual C.Cx)
  set b := Module.finrank (ZMod 2) (codeDual C.Cz)
  have hnr : (n : ℝ) > 0 := by exact_mod_cast hn
  have hr : 16 * n * r ≤ (k - 1) ^ 2 := by
    have h1 : (r : ℝ) ≤ 2*c1*eps1*n := Nat.floor_le (by positivity)
    have h2 : (2*c1*eps1*n : ℝ) ≤ (((k : ℝ)-1)/(4*n))^2 * n :=
      mul_le_mul_of_nonneg_right hcutoff hnr.le
    have h3 : (((k : ℝ)-1)/(4*n))^2 * n * (16 * n) = ((k:ℝ)-1)^2 := by
      field_simp; ring
    have h4 : ((16 * n * r : ℕ) : ℝ) ≤ (((k - 1) ^ 2 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hk]
      nlinarith
    exact_mod_cast h4
  have hV := s199o_vol n (k - 1) r hn (by omega) hr
  have hprod : (Bz.card : ℝ) * Bx.card ≤ 2 ^ (a + b) * (s199o_V n r : ℝ) ^ 2 := by
    have : Bz.card * Bx.card ≤ 2 ^ (a + b) * s199o_V n r ^ 2 := by
      calc Bz.card * Bx.card ≤ (2 ^ a * s199o_V n r) * (2 ^ b * s199o_V n r) := by
            rw [← hSz, ← hSx]; exact Nat.mul_le_mul hBz hBx
        _ = _ := by ring
    exact_mod_cast this
  have hfin : (Bz.card : ℝ) * Bx.card ≤ 2 ^ n / 2 := by
    calc _ ≤ 2 ^ (a + b) * (s199o_V n r : ℝ) ^ 2 := hprod
      _ ≤ 2 ^ (a + b) * 2 ^ (k - 1) := mul_le_mul_of_nonneg_left hV (by positivity)
      _ = 2 ^ n / 2 := by
        rw [← pow_add, eq_div_iff (by norm_num), ← pow_succ]
        congr 1; omega
  rw [div_le_iff₀ (by positivity)]
  linarith
