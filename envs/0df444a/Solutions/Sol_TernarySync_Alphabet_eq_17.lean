-- Prove2me | solution 1 for TernarySync.Alphabet.eq_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:33:27.347988+00:00
-- url     : https://prove2.me/submissions/1044a965-ff4b-4fc7-ade8-8e914d088d71

import Mathlib
import Definitions.Def_TernarySync_Alphabet_RandomSource
import Theorems.Thm_TernarySync_Alphabet_theorem_2_3
import Theorems.Thm_TernarySync_Alphabet_proposition_3_1
import Theorems.Thm_TernarySync_Alphabet_eq_14
import Theorems.Thm_TernarySync_Alphabet_eq_16

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace TernarySync.Dev.Eq17
open TernarySync.Alphabet

theorem codeword_length : ∀ (a : Fin 3) (r : Fin 2), (codeword a r).length = 18 := by decide

theorem W_cons (a : Fin 3) (T : List (Fin 3)) (R : Fin (a :: T).length → Fin 2) :
    W (a :: T) R = codeword a (R 0) ++ W T (fun i => R i.succ) := by
  simp [W, List.ofFn_succ]

theorem W_length : ∀ (T : List (Fin 3)) (R : Fin T.length → Fin 2), (W T R).length = 18 * T.length
  | [], R => by simp [W]
  | a :: T, R => by
    rw [W_cons, List.length_append, codeword_length, W_length T]
    simp; ring

theorem getW : ∀ (T : List (Fin 3)) (R : Fin T.length → Fin 2) (i : Fin T.length) (j : ℕ),
    j < 18 → (W T R)[18 * i.val + j]? = (codeword (T.get i) (R i))[j]?
  | [], R, i, j, hj => i.elim0
  | a :: T, R, i, j, hj => by
    rw [W_cons]
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add]
      rw [List.getElem?_append_left (by rw [codeword_length]; exact hj)]
      rfl
    | succ i' =>
      have h18 : (codeword a (R 0)).length = 18 := codeword_length _ _
      rw [List.getElem?_append_right (by rw [h18]; simp; omega)]
      rw [h18]
      have := getW T (fun i => R i.succ) i' j hj
      rw [show 18 * (i'.succ).val + j - 18 = 18 * i'.val + j by simp [Fin.val_succ]; omega]
      exact this

theorem fac_getElem? {α : Type*} (S : List α) (a b k : ℕ) :
    (factor S a b)[k]? = if k < b - a then S[a + k]? else none := by
  simp [factor, List.getElem?_take, List.getElem?_drop]

theorem factor_congr (T : List (Fin 3)) (R R' : Fin T.length → Fin 2) (a b : ℕ)
    (h : ∀ i : Fin T.length, a < 18 * i.val + 18 → 18 * i.val < b → R i = R' i) :
    factor (W T R) a b = factor (W T R') a b := by
  apply List.ext_getElem?
  intro k
  rw [fac_getElem?, fac_getElem?]
  by_cases hk : k < b - a
  · simp only [hk, if_true]
    by_cases hp : a + k < 18 * T.length
    · have hlt : (a + k) / 18 < T.length := by omega
      have e : a + k = 18 * ((⟨(a + k) / 18, hlt⟩ : Fin T.length).val) + (a + k) % 18 := by
        simp; omega
      rw [e, getW T R _ _ (by omega), getW T R' _ _ (by omega),
        h ⟨(a + k) / 18, hlt⟩ (by simp; omega) (by simp; omega)]
    · rw [List.getElem?_eq_none (by rw [W_length]; omega),
        List.getElem?_eq_none (by rw [W_length]; omega)]
  · simp [hk]

/-- the bad event only depends on the coordinates in `eventVars`. -/
theorem badEvent_dep (T : List (Fin 3)) (t ℓ : ℕ) (R R' : Fin T.length → Fin 2)
    (h : ∀ i ∈ eventVars T.length t ℓ, R i = R' i) (hR : R ∈ badEvent T t ℓ) :
    R' ∈ badEvent T t ℓ := by
  have h1 : factor (W T R) t (t + ℓ) = factor (W T R') t (t + ℓ) :=
    factor_congr T R R' _ _ (fun i h1 h2 => h i (by simp [eventVars]; omega))
  have h2 : factor (W T R) (t + ℓ) (t + 2 * ℓ) = factor (W T R') (t + ℓ) (t + 2 * ℓ) :=
    factor_congr T R R' _ _ (fun i h1 h2 => h i (by simp [eventVars]; omega))
  simpa [badEvent, blockX, blockY, h1, h2] using hR

/-- uniform measure on choice vectors -/
noncomputable def mu (N : ℕ) : Measure (Fin N → Fin 2) :=
  Measure.pi (fun _ => (PMF.uniformOfFintype (Fin 2)).toMeasure)

instance (N : ℕ) : IsProbabilityMeasure (mu N) := by unfold mu; infer_instance

theorem mu_real (N : ℕ) (A : Set (Fin N → Fin 2)) : (mu N).real A = unifProb A := by
  classical
  have hA : A = ↑(Finset.univ.filter fun R => R ∈ A) := by ext; simp
  have h1 : ∀ R : Fin N → Fin 2, mu N {R} = (1 / 2 : ENNReal) ^ N := by
    intro R
    unfold mu
    rw [Measure.pi_singleton]
    simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  unfold unifProb Measure.real
  conv_lhs => rw [hA]
  rw [← sum_measure_singleton]
  simp only [h1, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.toReal_mul]
  simp [div_eq_mul_inv]


theorem one_sub_ge (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-2 * x) ≤ 1 - x := by
  have hp : 0 < 1 - x := by linarith
  rw [← Real.le_log_iff_exp_le hp]
  have h := Real.log_le_sub_one_of_pos (inv_pos.2 hp)
  rw [Real.log_inv] at h
  have : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    rw [inv_eq_one_div, div_sub_one hp.ne', div_le_iff₀ hp]
    nlinarith
  linarith

/-- measurability of the bad event for the sigma algebra of its variables. -/
theorem hdet_aux (T : List (Fin 3)) (t ℓ : ℕ) :
    MeasurableSet[⨆ v ∈ eventVars T.length t ℓ, MeasurableSpace.comap
      (fun R : Fin T.length → Fin 2 => R v) inferInstance] (badEvent T t ℓ) := by
  classical
  set m : MeasurableSpace (Fin T.length → Fin 2) := ⨆ v ∈ eventVars T.length t ℓ,
    MeasurableSpace.comap (fun R : Fin T.length → Fin 2 => R v) inferInstance with hm
  have hv : ∀ v ∈ eventVars T.length t ℓ, ∀ c : Fin 2, MeasurableSet[m] {R : Fin T.length → Fin 2 | R v = c} := by
    intro v hv c
    have hle : MeasurableSpace.comap (fun R : Fin T.length → Fin 2 => R v) inferInstance ≤ m :=
      le_iSup₂ (f := fun v (_ : v ∈ eventVars T.length t ℓ) =>
        MeasurableSpace.comap (fun R : Fin T.length → Fin 2 => R v) inferInstance) v hv
    exact hle _ ⟨{c}, measurableSet_singleton c, rfl⟩
  have heq : badEvent T t ℓ = ⋃ b ∈ (Finset.univ.filter fun b => b ∈ badEvent T t ℓ),
      ⋂ v ∈ eventVars T.length t ℓ, {R : Fin T.length → Fin 2 | R v = b v} := by
    ext R
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · intro hR; exact ⟨R, hR, fun v _ => rfl⟩
    · rintro ⟨b, hb, hRb⟩
      exact badEvent_dep T t ℓ b R (fun i hi => (hRb i hi).symm) hb
  rw [heq]
  refine @Finset.measurableSet_biUnion _ _ m _ _ (fun b _ => ?_)
  exact @Finset.measurableSet_biInter _ _ m _ _ (fun v hv' => hv v hv' (b v))


theorem avail_iff (N t ℓ : ℕ) : (t, ℓ) ∈ availEvents N ↔ 1000 < ℓ ∧ t + 2 * ℓ ≤ 18 * N := by
  simp only [availEvents, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem long_exists (T : List (Fin 3)) (hT : IsSquareFree T) :
    ∃ R : Fin T.length → Fin 2, ∀ p ∈ availEvents T.length, R ∉ badEvent T p.1 p.2 := by
  classical
  set N := T.length with hN
  have hind : iIndepFun (fun (v : Fin N) (R : Fin N → Fin 2) => R v) (mu N) :=
    iIndepFun_pi (X := fun _ => (id : Fin 2 → Fin 2)) (fun _ => aemeasurable_id)
  have hx : ∀ i : {p // p ∈ availEvents N},
      0 < Real.exp (-(i.1.2 : ℝ) / 80) ∧ Real.exp (-(i.1.2 : ℝ) / 80) < 1 := by
    intro i
    have h := (avail_iff N i.1.1 i.1.2).1 (by simp)
    refine ⟨Real.exp_pos _, ?_⟩
    rw [← Real.exp_zero]; apply Real.exp_lt_exp.2
    have : (0 : ℝ) < i.1.2 := by exact_mod_cast (by omega : 0 < i.1.2)
    linarith
  have key := theorem_2_3 (mu N) (V := Fin N) (β := fun _ => Fin 2)
    (fun v R => R v) (fun v => measurable_pi_apply v) hind
    (ι := {p // p ∈ availEvents N}) (fun i => badEvent T i.1.1 i.1.2)
    (fun i => eventVars N i.1.1 i.1.2) (fun i => hdet_aux T i.1.1 i.1.2)
    (fun i => Real.exp (-(i.1.2 : ℝ) / 80)) hx ?_
  · have hpos := key.2
    have hpos' : 0 < (mu N).real (⋂ i : {p // p ∈ availEvents N}, (badEvent T i.1.1 i.1.2)ᶜ) :=
      lt_of_lt_of_le hpos key.1
    have hne : (⋂ i : {p // p ∈ availEvents N}, (badEvent T i.1.1 i.1.2)ᶜ).Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      rw [hc] at hpos'
      simp at hpos'
    obtain ⟨R, hR⟩ := hne
    refine ⟨R, fun p hp => ?_⟩
    have := Set.mem_iInter.1 hR ⟨p, hp⟩
    exact this
  · intro i
    obtain ⟨⟨t, ℓ⟩, hi⟩ := i
    have hmem : (t, ℓ) ∈ availEvents N := hi
    obtain ⟨hl, ht⟩ := (avail_iff N t ℓ).1 hmem
    have hprob : (mu N).real (badEvent T t ℓ) < Real.exp (-(9 * (ℓ : ℝ)) / 500) := by
      rw [mu_real]; exact eq_14 T hT t ℓ hl ht
    have hprod : ∏ j ∈ Finset.univ.filter (fun j : {p // p ∈ availEvents N} =>
          j ≠ ⟨(t, ℓ), hi⟩ ∧
          (eventVars N j.1.1 j.1.2 ∩ eventVars N (t, ℓ).1 (t, ℓ).2).Nonempty),
        (1 - Real.exp (-(j.1.2 : ℝ) / 80)) =
        ∏ p ∈ neighbours N t ℓ, (1 - Real.exp (-(p.2 : ℝ) / 80)) := by
      refine Finset.prod_bij (fun j _ => j.1) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [neighbours, Finset.mem_filter]
        refine ⟨j.2, fun h => hj.1 (Subtype.ext h), hj.2⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro p hp
        simp only [neighbours, Finset.mem_filter] at hp
        refine ⟨⟨p, hp.1⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => hp.2.1 (congrArg Subtype.val h), hp.2.2⟩
      · intro j _; rfl
    show (mu N).real (badEvent T t ℓ) ≤ Real.exp (-(ℓ : ℝ) / 80) * ∏ j ∈ Finset.univ.filter
      (fun j : {p // p ∈ availEvents N} => j ≠ ⟨(t, ℓ), hi⟩ ∧
        (eventVars N j.1.1 j.1.2 ∩ eventVars N (t, ℓ).1 (t, ℓ).2).Nonempty),
        (1 - Real.exp (-(j.1.2 : ℝ) / 80))
    rw [hprod]
    obtain ⟨hs1, hs2⟩ := eq_16 N t ℓ hmem
    have hsum : ∑ p ∈ neighbours N t ℓ, Real.exp (-(p.2 : ℝ) / 80) ≤ (ℓ : ℝ) / 490 :=
      le_trans (le_trans hs1 hs2.le) le_rfl
    have hhalf : ∀ p ∈ neighbours N t ℓ, Real.exp (-(p.2 : ℝ) / 80) ≤ 1 / 2 := by
      intro p hp
      have hp' : p ∈ availEvents N := (Finset.mem_filter.1 hp).1
      have h := ((avail_iff N p.1 p.2).1 (by simpa using hp')).1
      have h1 : (1000 : ℝ) < p.2 := by exact_mod_cast h
      have : Real.exp (-(p.2 : ℝ) / 80) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      rw [Real.exp_neg] at this
      have h3 : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) h2
      linarith
    have hge : Real.exp (-2 * ((ℓ : ℝ) / 490)) ≤
        ∏ p ∈ neighbours N t ℓ, (1 - Real.exp (-(p.2 : ℝ) / 80)) := by
      calc Real.exp (-2 * ((ℓ : ℝ) / 490)) ≤
            Real.exp (-2 * ∑ p ∈ neighbours N t ℓ, Real.exp (-(p.2 : ℝ) / 80)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = ∏ p ∈ neighbours N t ℓ, Real.exp (-2 * Real.exp (-(p.2 : ℝ) / 80)) := by
            rw [Finset.mul_sum, Real.exp_sum]
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
            (fun p hp => one_sub_ge _ (Real.exp_pos _).le (hhalf p hp))
    have hl' : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
    calc (mu N).real (badEvent T t ℓ) ≤ Real.exp (-(9 * (ℓ : ℝ)) / 500) := hprob.le
      _ ≤ Real.exp (-(ℓ : ℝ) / 80) * Real.exp (-2 * ((ℓ : ℝ) / 490)) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hge (Real.exp_pos _).le


theorem factor_infix {α : Type*} (S : List α) (i j : ℕ) : factor S i j <:+: S :=
  ((List.take_prefix _ _).isInfix).trans (List.drop_suffix _ _).isInfix

theorem factor_length (T : List (Fin 3)) (R : Fin T.length → Fin 2) (a b : ℕ)
    (h : b ≤ 18 * T.length) : (factor (W T R) a b).length = b - a := by
  simp [factor, W_length]
  omega

theorem lcs_le_len {α : Type*} (x y : List α) : lcs x y ≤ x.length := by
  unfold lcs
  refine csSup_le ⟨0, [], by simp⟩ ?_
  rintro k ⟨z, hz, _, rfl⟩
  exact hz.length_le

theorem lcs_eq_len {α : Type*} (x y : List α) (h : lcs x y = x.length) (hl : x.length = y.length) :
    x = y := by
  have hne : {k : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k}.Nonempty :=
    ⟨0, [], by simp⟩
  have hbdd : BddAbove {k : ℕ | ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k} :=
    ⟨x.length, by rintro k ⟨z, hz, _, rfl⟩; exact hz.length_le⟩
  obtain ⟨z, hz1, hz2, hz3⟩ := Nat.sSup_mem hne hbdd
  change z.length = lcs x y at hz3
  rw [h] at hz3
  rw [← hz1.eq_of_length hz3, ← hz2.eq_of_length (hz3.trans hl)]

theorem short_ok (T : List (Fin 3)) (hT : IsSquareFree T) (R : Fin T.length → Fin 2)
    (t ℓ : ℕ) (h1 : 1 ≤ ℓ) (h2 : ℓ ≤ 1000) (ht : t + 2 * ℓ ≤ 18 * T.length) :
    (lcs (blockX T R t ℓ) (blockY T R t ℓ) : ℝ) ≤ (1 - (1 : ℝ) / 1000) * (ℓ : ℝ) := by
  have hX : (blockX T R t ℓ).length = ℓ := by
    unfold blockX; rw [factor_length T R _ _ (by omega)]; omega
  have hY : (blockY T R t ℓ).length = ℓ := by
    unfold blockY; rw [factor_length T R _ _ (by omega)]; omega
  have hle : lcs (blockX T R t ℓ) (blockY T R t ℓ) ≤ ℓ := by have := lcs_le_len (blockX T R t ℓ) (blockY T R t ℓ); omega
  have hne : lcs (blockX T R t ℓ) (blockY T R t ℓ) ≠ ℓ := by
    intro heq
    have hXY : blockX T R t ℓ = blockY T R t ℓ :=
      lcs_eq_len _ _ (by rw [heq, hX]) (by rw [hX, hY])
    have hsq := (proposition_3_1.2.1 T hT R) (factor (W T R) t (t + 2 * ℓ)) (factor_infix _ _ _)
    apply hsq
    refine ⟨blockX T R t ℓ, ?_, ?_⟩
    · intro hc; rw [hc] at hX; simp at hX; omega
    · have hcat : factor (W T R) t (t + 2 * ℓ) = blockX T R t ℓ ++ blockY T R t ℓ := by
        unfold blockX blockY factor
        rw [show t + 2 * ℓ - t = ℓ + ℓ by omega, List.take_add,
          show t + 2 * ℓ - (t + ℓ) = ℓ by omega, show t + ℓ - t = ℓ by omega,
          List.drop_drop]
      rw [hcat, ← hXY]
  have : lcs (blockX T R t ℓ) (blockY T R t ℓ) + 1 ≤ ℓ := by omega
  have : ((lcs (blockX T R t ℓ) (blockY T R t ℓ) : ℕ) : ℝ) + 1 ≤ ℓ := by exact_mod_cast this
  have h3 : (ℓ : ℝ) ≤ 1000 := by exact_mod_cast h2
  nlinarith


end TernarySync.Dev.Eq17

namespace TernarySync.Alphabet
open TernarySync.Dev.Eq17 in
theorem chk_eq_17 (T : List (Fin 3)) (hT : IsSquareFree T) :
    ∃ R : Fin T.length → Fin 2, ∀ t ℓ : ℕ, 1 ≤ ℓ → t + 2 * ℓ ≤ 18 * T.length →
      (lcs (blockX T R t ℓ) (blockY T R t ℓ) : ℝ) ≤ (1 - (1 : ℝ) / 1000) * (ℓ : ℝ) := by
  obtain ⟨R, hR⟩ := long_exists T hT
  refine ⟨R, fun t ℓ h1 ht => ?_⟩
  by_cases hl : 1000 < ℓ
  · have hm : (t, ℓ) ∈ availEvents T.length := (avail_iff _ _ _).2 ⟨hl, ht⟩
    have := hR _ hm
    simp only [badEvent, Set.mem_ofPred_eq, not_lt] at this
    exact this
  · exact short_ok T hT R t ℓ h1 (by omega) ht

end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_eq_17 := @TernarySync.Alphabet.chk_eq_17
