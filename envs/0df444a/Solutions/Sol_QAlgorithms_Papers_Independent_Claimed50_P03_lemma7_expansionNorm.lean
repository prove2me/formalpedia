-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma7_expansionNorm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T12:00:20.042002+00:00
-- url     : https://prove2.me/submissions/9b104d83-0153-42f4-aa0d-071cf45461c4

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

theorem g58a_lemma6 (n de : ℕ) (hn : 1 ≤ n) (hde : 1 ≤ de) (hden : de ≤ n)
    (ce : ℝ) (hce : 1 ≤ ce) (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian)
    (hexp : HasExpansion H ce de) (pi : Equiv.Perm (Fin n)) (i : Fin n) :
    ((Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      P (pi i) ≠ 0 ∧ ∀ j : Fin n, i < j → P (pi j) = 0).card : ℝ) ≤
      ce * ((i.val + 1 : ℕ) : ℝ) ^ (de - 1) := by
  set F := (Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      P (pi i) ≠ 0 ∧ ∀ j : Fin n, i < j → P (pi j) = 0) with hF
  set T : Finset (Fin n) := Finset.univ.filter fun x => pi.symm x ≤ i with hT
  have hTcard : T.card = i.val + 1 := by
    have : T = (Finset.Iic i).map pi.toEmbedding := by
      ext x; simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_Iic, Equiv.toEmbedding_apply]
      constructor
      · intro h; exact ⟨pi.symm x, h, by simp⟩
      · rintro ⟨a, ha, rfl⟩; simpa using ha
    rw [this, Finset.card_map, Fin.card_Iic]
  have hpiT : pi i ∈ T := by simp [hT]
  -- support facts
  have hsuppT : ∀ P ∈ F, wordSupport P ⊆ T := by
    intro P hP x hx
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra h
    push Not at h
    exact hx (by simpa using hP.2.2 _ h)
  have hpisupp : ∀ P ∈ F, pi i ∈ wordSupport P := by
    intro P hP
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    simp [wordSupport, hP.2.1]
  set G : Finset (Fin n) → Finset (Fin n → Fin 4) := fun S =>
    Finset.univ.filter fun P : (Fin n → Fin 4) => coefficient H P ≠ 0 ∧
      (S ⊆ wordSupport P ∨ wordSupport P ⊆ S) with hG
  have hcoef : ∀ P ∈ F, coefficient H P ≠ 0 := by
    intro P hP
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    exact hP.1
  have key : ∀ (𝒮 : Finset (Finset (Fin n))), (∀ S ∈ 𝒮, S.card = de) → F ⊆ 𝒮.biUnion G →
      (F.card : ℝ) ≤ 𝒮.card * ce := by
    intro 𝒮 h𝒮 hsub
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h1' : (F.card : ℝ) ≤ ∑ S ∈ 𝒮, ((G S).card : ℝ) := by exact_mod_cast h1
    refine h1'.trans ?_
    have := Finset.sum_le_card_nsmul 𝒮 (fun S => ((G S).card : ℝ)) ce
      (fun S hS => hexp S (h𝒮 S hS))
    simpa using this
  have hpow1 : (1 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) ^ (de - 1) :=
    one_le_pow₀ (by exact_mod_cast Nat.succ_pos _ |>.nat_succ_le)
  by_cases hcase : de ≤ i.val + 1
  · set 𝒮 := (T.powersetCard de).filter (fun S => pi i ∈ S) with h𝒮
    have hmem : ∀ S ∈ 𝒮, S.card = de ∧ pi i ∈ S ∧ S ⊆ T := by
      intro S hS
      simp only [h𝒮, Finset.mem_filter, Finset.mem_powersetCard] at hS
      exact ⟨hS.1.2, hS.2, hS.1.1⟩
    have hsub : F ⊆ 𝒮.biUnion G := by
      intro P hP
      simp only [Finset.mem_biUnion]
      have hc := hcoef P hP
      by_cases hs : de ≤ (wordSupport P).card
      · obtain ⟨S, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq
          (Finset.singleton_subset_iff.mpr (hpisupp P hP)) (by simpa using hde) hs
        refine ⟨S, ?_, ?_⟩
        · simp only [h𝒮, Finset.mem_filter, Finset.mem_powersetCard]
          exact ⟨⟨h2.trans (hsuppT P hP), h3⟩, Finset.singleton_subset_iff.mp h1⟩
        · simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hc, Or.inl h2⟩
      · push Not at hs
        obtain ⟨S, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq
          (hsuppT P hP) hs.le (by rw [hTcard]; exact hcase)
        refine ⟨S, ?_, ?_⟩
        · simp only [h𝒮, Finset.mem_filter, Finset.mem_powersetCard]
          exact ⟨⟨h2, h3⟩, h1 (hpisupp P hP)⟩
        · simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hc, Or.inr h1⟩
    have hk := key 𝒮 (fun S hS => (hmem S hS).1) hsub
    have hcard : 𝒮.card ≤ (i.val + 1) ^ (de - 1) := by
      have : 𝒮.card ≤ ((T.erase (pi i)).powersetCard (de - 1)).card := by
        apply Finset.card_le_card_of_injOn (fun S => S.erase (pi i))
        · intro S hS
          obtain ⟨h1, h2, h3⟩ := hmem S hS
          simp only [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨Finset.erase_subset_erase _ h3, ?_⟩
          rw [Finset.card_erase_of_mem h2, h1]
        · intro S hS S' hS' h
          have a := (hmem S hS).2.1
          have b := (hmem S' hS').2.1
          simp only at h
          rw [← Finset.insert_erase a, ← Finset.insert_erase b, h]
      rw [Finset.card_powersetCard, Finset.card_erase_of_mem hpiT, hTcard] at this
      refine this.trans ((Nat.choose_le_pow _ _).trans ?_)
      exact Nat.pow_le_pow_left (by omega) _
    have hcR : (𝒮.card : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) ^ (de - 1) := by exact_mod_cast hcard
    nlinarith
  · push Not at hcase
    obtain ⟨S, h1, -, h3⟩ := Finset.exists_subsuperset_card_eq (n := de)
      (Finset.subset_univ T) (by rw [hTcard]; exact hcase.le) (by simpa using hden)
    have hsub : F ⊆ ({S} : Finset (Finset (Fin n))).biUnion G := by
      intro P hP
      simp only [Finset.singleton_biUnion, hG, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hcoef P hP, Or.inr ((hsuppT P hP).trans h1)⟩
    have hk := key {S} (by simpa using h3) hsub
    simp at hk
    nlinarith


lemma g58a_concave {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (β : ℝ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∑ i ∈ s, x i ^ β ≤ (s.card : ℝ) ^ (1 - β) * (∑ i ∈ s, x i) ^ β := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow s (fun i => x i ^ β) (p := 1 / β)
    (by rw [le_div_iff₀ hβ0]; linarith)
  have e1 : ∀ i ∈ s, |x i ^ β| = x i ^ β := fun i hi => abs_of_nonneg (Real.rpow_nonneg (hx i hi) _)
  have e2 : ∀ i ∈ s, |x i ^ β| ^ (1 / β) = x i := by
    intro i hi
    rw [e1 i hi, ← Real.rpow_mul (hx i hi), mul_one_div_cancel hβ0.ne', Real.rpow_one]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at h
  have hS : 0 ≤ ∑ i ∈ s, x i ^ β := Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hx i hi) _
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hS _) h hβ0.le
  rw [← Real.rpow_mul hS, one_div_mul_cancel hβ0.ne', Real.rpow_one] at h2
  refine h2.trans (le_of_eq ?_)
  rw [Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Finset.sum_nonneg fun i hi => hx i hi), ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 2
  field_simp

lemma g58a_anti {n : ℕ} (a : Fin n → ℝ) (ha : Antitone a) (h0 : ∀ j, 0 ≤ a j) (j : Fin n) :
    ((j.val + 1 : ℕ) : ℝ) * a j ≤ ∑ l, a l := by
  have h1 : ∑ l ∈ Finset.Iic j, a j ≤ ∑ l ∈ Finset.Iic j, a l :=
    Finset.sum_le_sum fun l hl => ha (Finset.mem_Iic.mp hl)
  rw [Finset.sum_const, Fin.card_Iic, nsmul_eq_mul] at h1
  exact h1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ => h0 l)

theorem solution (n de q : ℕ) (hn : 1 ≤ n) (hde : 1 ≤ de)
    (hden : de ≤ n) (hq : 1 ≤ q) (ce : ℝ) (hce : 1 ≤ ce)
    (H : (Matrix (Qubits n) (Qubits n) ℂ)) (hH : H.IsHermitian) (hexp : HasExpansion H ce de) :
    sliceMass q (expansionExponent de) H / Real.rpow ce (1 / (2 * (de : ℝ))) ≤
      ∑ i : Fin n, Real.sqrt
        (∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q ∧ P i ≠ 0),
          coefficient H P ^ 2) := by
  set d : ℝ := (de : ℝ) with hd
  have hd1 : 1 ≤ d := by rw [hd]; exact_mod_cast hde
  set r := expansionExponent de with hr
  have hr' : r = 2 * d / (d + 1) := rfl
  have hrpos : 0 < r := by rw [hr']; positivity
  set β : ℝ := d / (d + 1) with hβ
  set γ : ℝ := (d - 1) / (d + 1) with hγ
  set α : ℝ := 1 / (d + 1) with hα
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 := by rw [hβ, div_le_one (by linarith)]; linarith
  have hγ0 : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
  have hα0 : 0 ≤ α := by positivity
  have hαβ : 1 - β = α := by rw [hα, hβ]; field_simp; ring
  have hrβ : r = 2 * β := by rw [hr', hβ]; ring
  have h2β : 2 * β = 1 + γ := by rw [hβ, hγ]; field_simp; ring
  set W : Fin n → ℝ := fun i => ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) =>
    pauliWeight P = q ∧ P i ≠ 0), coefficient H P ^ 2 with hW
  have hW0 : ∀ i, 0 ≤ W i := fun i => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set π := Tuple.sort (fun i => -W i) with hπ
  have hmono := Tuple.monotone_sort (fun i => -W i)
  set a : Fin n → ℝ := fun j => Real.sqrt (W (π j)) with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => Real.sqrt_nonneg _
  have hanti : Antitone a := by
    intro x y hxy
    have := hmono hxy
    simp only [Function.comp, neg_le_neg_iff] at this
    exact Real.sqrt_le_sqrt this
  set S := ∑ i : Fin n, Real.sqrt (W i) with hS
  have hSa : S = ∑ j, a j := (Equiv.sum_comp π (fun i => Real.sqrt (W i))).symm
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  -- groups
  set G : Fin n → Finset (Fin n → Fin 4) := fun j => Finset.univ.filter (fun P =>
    pauliWeight P = q ∧ coefficient H P ≠ 0 ∧ P (π j) ≠ 0 ∧ ∀ l, j < l → P (π l) = 0) with hG
  set f : (Fin n → Fin 4) → ℝ := fun P => Real.rpow |coefficient H P| r with hf
  have hsum : ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q), f P =
      ∑ j, ∑ P ∈ G j, f P := by
    rw [← Finset.sum_biUnion]
    · symm
      apply Finset.sum_subset
      · intro P hP
        simp only [Finset.mem_biUnion, hG, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
        obtain ⟨j, hj⟩ := hP; exact hj.1
      · intro P hP hPn
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
        by_contra hfP
        have hc : coefficient H P ≠ 0 := by
          intro hc; apply hfP; simp [hf, hc, Real.zero_rpow hrpos.ne']
        have hne : (Finset.univ.filter fun j => P (π j) ≠ 0).Nonempty := by
          by_contra hem
          rw [Finset.not_nonempty_iff_eq_empty] at hem
          have : wordSupport P = ∅ := by
            ext x
            simp only [wordSupport, Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.notMem_empty, iff_false, not_not]
            have := Finset.filter_eq_empty_iff.mp hem (Finset.mem_univ (π.symm x))
            simpa using this
          have h0 : pauliWeight P = 0 := by unfold pauliWeight; rw [this]; rfl
          omega
        obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image _ id hne
        apply hPn
        simp only [Finset.mem_biUnion, hG, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨j, hP, hc, (Finset.mem_filter.mp hj).2, fun l hl => ?_⟩
        by_contra hl'
        have := hjmax l (by simp [hl'])
        exact absurd hl (not_lt.mpr this)
    · intro j _ l _ hjl
      rw [Function.onFun, Finset.disjoint_left]
      intro P hPj hPl
      simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hPj hPl
      rcases lt_or_gt_of_ne hjl with h | h
      · exact hPl.2.2.1 (hPj.2.2.2 l h)
      · exact hPj.2.2.1 (hPl.2.2.2 j h)
  have hce0 : 0 < ce := by linarith
  have hgroup : ∀ j, ∑ P ∈ G j, f P ≤ ce ^ α * a j * S ^ γ := by
    intro j
    have hfP : ∀ P ∈ G j, f P = (coefficient H P ^ 2) ^ β := by
      intro P _
      simp only [hf]
      rw [show Real.rpow |coefficient H P| r = |coefficient H P| ^ r from rfl, hrβ,
        Real.rpow_mul (abs_nonneg _), Real.rpow_two, sq_abs]
    rw [Finset.sum_congr rfl hfP]
    have h1 := g58a_concave (G j) (fun P => coefficient H P ^ 2) (fun _ _ => sq_nonneg _) β hβ0 hβ1
    rw [hαβ] at h1
    refine h1.trans ?_
    have hcard : ((G j).card : ℝ) ≤ ce * ((j.val + 1 : ℕ) : ℝ) ^ (de - 1) := by
      refine le_trans ?_ (g58a_lemma6 n de hn hde hden ce hce H hH hexp π j)
      exact_mod_cast Finset.card_le_card (fun P hP => by
        simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
        exact hP.2)
    have hsumW : ∑ P ∈ G j, coefficient H P ^ 2 ≤ W (π j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro P hP
        simp only [hG, hW, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
        exact ⟨hP.1, hP.2.2.1⟩
      · intro _ _ _; exact sq_nonneg _
    set m : ℝ := ((j.val + 1 : ℕ) : ℝ) with hm
    have hm0 : 0 ≤ m := by positivity
    calc ((G j).card : ℝ) ^ α * (∑ P ∈ G j, coefficient H P ^ 2) ^ β
        ≤ (ce * m ^ (de - 1)) ^ α * (W (π j)) ^ β := by
          gcongr
      _ = ce ^ α * a j * ((m * a j) ^ γ) := by
          have hWa : W (π j) = a j ^ 2 := by rw [ha]; simp only; rw [Real.sq_sqrt (hW0 _)]
          rw [hWa, Real.mul_rpow hce0.le (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hm0, ← Real.rpow_two, ← Real.rpow_mul (ha0 j), h2β,
            Real.rpow_add' (ha0 j) (by linarith), Real.rpow_one, Real.mul_rpow hm0 (ha0 j)]
          have : ((de - 1 : ℕ) : ℝ) * α = γ := by
            rw [Nat.cast_sub hde, hγ, hα, ← hd]; field_simp; ring
          rw [this]; ring
      _ ≤ ce ^ α * a j * S ^ γ := by
          gcongr
          rw [hSa]; exact g58a_anti a hanti ha0 j
  have htot : ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q), f P ≤
      ce ^ α * S ^ r := by
    rw [hsum]
    refine (Finset.sum_le_sum fun j _ => hgroup j).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← hSa, hrβ, h2β,
      Real.rpow_add' hS0 (by linarith), Real.rpow_one]
    ring
  have hpos : 0 < Real.rpow ce (1 / (2 * (de : ℝ))) := Real.rpow_pos_of_pos hce0 _
  rw [div_le_iff₀ hpos]
  unfold sliceMass
  have hsum0 : 0 ≤ ∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q), f P :=
    Finset.sum_nonneg fun P _ => Real.rpow_nonneg (abs_nonneg _) _
  calc Real.rpow (∑ P ∈ Finset.univ.filter (fun P : (Fin n → Fin 4) => pauliWeight P = q),
        Real.rpow |coefficient H P| r) (1 / r)
      ≤ (ce ^ α * S ^ r) ^ (1 / r) := Real.rpow_le_rpow hsum0 htot (by positivity)
    _ = S * Real.rpow ce (1 / (2 * (de : ℝ))) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hce0.le _) (Real.rpow_nonneg hS0 _),
          ← Real.rpow_mul hce0.le, ← Real.rpow_mul hS0, mul_one_div_cancel hrpos.ne', Real.rpow_one,
          mul_comm]
        congr 1
        show ce ^ (α * (1 / r)) = ce ^ (1 / (2 * d))
        congr 1
        rw [hα, hr']; field_simp

end
