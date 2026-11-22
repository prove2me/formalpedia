-- Prove2me | solution 1 for ProbMetricStab.MixedInt.lemma_3_5_b
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:12:27.68516+00:00
-- url     : https://prove2.me/submissions/f938222d-5f72-4729-86b4-193f5091ce4e

import Mathlib
import Definitions.Def_ProbMetricStab_MixedInt_Setting

open MeasureTheory Matrix
open scoped ENNReal NNReal

section Helpers

open ProbMetricStab.MixedInt

/-! ### Step 1: Rational kernel lemma and integer ray generators for rational cones -/

private lemma exists_rat_ker_of_real_ker {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MQ : Matrix (Fin r) ι ℚ) (S : Finset ι)
    (x : ι → ℝ) (hxne : x ≠ 0) (hxS : ∀ j ∉ S, x j = 0)
    (hxker : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ x = 0) :
    ∃ q : ι → ℚ, q ≠ 0 ∧ (∀ j ∉ S, q j = 0) ∧ MQ *ᵥ q = 0 := by
  let BQ : Matrix (Fin r) S ℚ := fun i j => MQ i j.1
  let B : Matrix (Fin r) S ℝ := BQ.map (Rat.castHom ℝ)
  let xS : S → ℝ := fun j => x j.1
  have hxSne : xS ≠ 0 := by
    intro h0
    apply hxne
    ext j
    simp only [Pi.zero_apply]
    by_cases hj : j ∈ S
    · simpa [xS] using congr_fun h0 ⟨j, hj⟩
    · exact hxS j hj
  have hBxS : B *ᵥ xS = 0 := by
    ext i
    have hi := congr_fun hxker i
    simp only [mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply] at hi ⊢
    calc ∑ j : S, B i j * xS j
        = ∑ j : S, (MQ i j.1 : ℝ) * x j.1 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [B, xS]
          rw [Matrix.map_apply]
          rfl
      _ = ∑ j ∈ S, (MQ i j : ℝ) * x j := by
          rw [← Finset.sum_attach S (fun j => (MQ i j : ℝ) * x j)]
          rfl
      _ = ∑ j : ι, (MQ i j : ℝ) * x j := by
          apply Finset.sum_subset (Finset.subset_univ S)
          intro j _ hj
          simp [hxS j hj]
      _ = 0 := hi
  have hker_ne : LinearMap.ker (Matrix.toLin' BQ) ≠ ⊥ := by
    intro hker
    obtain ⟨g, hg⟩ := (Matrix.toLin' BQ).exists_leftInverse_of_injective hker
    let LQ : Matrix S (Fin r) ℚ := LinearMap.toMatrix' g
    have hmul : LQ * BQ = 1 := by
      rw [← LinearMap.toMatrix'_id, ← hg, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
    let LR : Matrix S (Fin r) ℝ := LQ.map (Rat.castHom ℝ)
    have hmulR : LR * B = 1 := by
      change LQ.map (Rat.castHom ℝ) * BQ.map (Rat.castHom ℝ) = 1
      rw [← Matrix.map_mul, hmul, Matrix.map_one (Rat.castHom ℝ) (map_zero _) (map_one _)]
    have hxS0 : xS = 0 := by
      calc xS = (1 : Matrix S S ℝ) *ᵥ xS := by simp
        _ = (LR * B) *ᵥ xS := by rw [hmulR]
        _ = LR *ᵥ (B *ᵥ xS) := by rw [Matrix.mulVec_mulVec]
        _ = LR *ᵥ 0 := by rw [hBxS]
        _ = 0 := by simp
    exact hxSne hxS0
  rw [Submodule.ne_bot_iff] at hker_ne
  obtain ⟨qS, hqSker, hqSne⟩ := hker_ne
  rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hqSker
  refine ⟨fun j => if h : j ∈ S then qS ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
  · intro h0
    apply hqSne
    ext ⟨j, hj⟩
    simpa [hj] using congr_fun h0 j
  · intro j hj
    simp [hj]
  · ext i
    have hi := congr_fun hqSker i
    simp only [mulVec, dotProduct, Pi.zero_apply] at hi ⊢
    calc ∑ j : ι, MQ i j * (if h : j ∈ S then qS ⟨j, h⟩ else 0)
        = ∑ j ∈ S, MQ i j * (if h : j ∈ S then qS ⟨j, h⟩ else 0) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro j _ hj
          simp [hj]
      _ = ∑ j ∈ S.attach, MQ i j.1 * qS j := by
          rw [← Finset.sum_attach S]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp [j.2]
      _ = ∑ j : S, BQ i j * qS j := rfl
      _ = 0 := hi

private lemma exists_nat_ray_of_one_dim {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MQ : Matrix (Fin r) ι ℚ) (S : Finset ι) (hSne : S.Nonempty)
    (w : ι → ℝ) (hw0 : 0 ≤ w) (hwS : ∀ j, j ∈ S ↔ 0 < w j)
    (hwker : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ w = 0)
    (h1 : ∀ u : ι → ℝ, (∀ j ∉ S, u j = 0) → MQ.map (Rat.cast : ℚ → ℝ) *ᵥ u = 0 →
      ∃ c : ℝ, u = c • w) :
    ∃ d : ι → ℕ, (∀ j, j ∈ S ↔ 0 < d j) ∧
      MQ.map (Rat.cast : ℚ → ℝ) *ᵥ (fun j => (d j : ℝ)) = 0 ∧
      (∀ u : ι → ℝ, (∀ j ∉ S, u j = 0) → MQ.map (Rat.cast : ℚ → ℝ) *ᵥ u = 0 →
        ∃ c : ℝ, u = c • (fun j => (d j : ℝ))) := by
  let M : Matrix (Fin r) ι ℝ := MQ.map (Rat.cast : ℚ → ℝ)
  have hwne : w ≠ 0 := by
    obtain ⟨j₀, hj₀⟩ := hSne
    intro h0
    have hpos : 0 < w j₀ := (hwS j₀).mp hj₀
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  have hwout : ∀ j ∉ S, w j = 0 := by
    intro j hj
    have hle : w j ≤ 0 := not_lt.mp (fun h => hj ((hwS j).mpr h))
    exact le_antisymm hle (hw0 j)
  obtain ⟨q, hqne, hqS, hqker⟩ := exists_rat_ker_of_real_ker MQ S w hwne hwout hwker
  let qR : ι → ℝ := fun j => (q j : ℝ)
  have hqRne : qR ≠ 0 := by
    intro h0
    apply hqne
    ext j
    have hj := congr_fun h0 j
    simp only [qR, Pi.zero_apply] at hj ⊢
    exact_mod_cast hj
  have hqRS : ∀ j ∉ S, qR j = 0 := by
    intro j hj
    simp [qR, hqS j hj]
  have hqRker : M *ᵥ qR = 0 := by
    ext i
    have hi := congr_fun hqker i
    have hiR : ((MQ *ᵥ q) i : ℝ) = 0 := by exact_mod_cast hi
    simpa [M, qR, mulVec, dotProduct] using hiR
  obtain ⟨c, hc⟩ := h1 qR hqRS hqRker
  have hcne : c ≠ 0 := by
    intro hc0
    rw [hc0, zero_smul] at hc
    exact hqRne hc
  let D : ℕ := ∏ j : ι, (q j).den
  have hDpos : 0 < D := Finset.prod_pos (fun j _ => (q j).pos)
  let z : ι → ℤ := fun j => (q j).num * ((D / (q j).den : ℕ) : ℤ)
  have hz_eq : ∀ j, (z j : ℝ) = (D : ℝ) * qR j := by
    intro j
    have hdvd : (q j).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hDmul : (D / (q j).den) * (q j).den = D := Nat.div_mul_cancel hdvd
    have hden_ne : ((q j).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q j).den_nz
    have hq_eq : (q j : ℝ) = ((q j).num : ℝ) / ((q j).den : ℝ) := by
      exact_mod_cast (q j).num_div_den.symm
    simp only [z, qR, Int.cast_mul, Int.cast_natCast]
    rw [hq_eq]
    have hDmulR : ((D / (q j).den : ℕ) : ℝ) * ((q j).den : ℝ) = (D : ℝ) := by
      exact_mod_cast hDmul
    field_simp [hden_ne]
    rw [mul_assoc, hDmulR]
  let s : ℤ := if 0 < c then 1 else -1
  let a : ℝ := (s : ℝ) * ((D : ℝ) * c)
  have hapos : 0 < a := by
    have hDR : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hDpos
    by_cases hcp : 0 < c
    · simp only [a, s, if_pos hcp, Int.cast_one, one_mul]
      exact mul_pos hDR hcp
    · have hcn : c < 0 := lt_of_le_of_ne (not_lt.mp hcp) hcne
      simp only [a, s, if_neg hcp, Int.cast_neg, Int.cast_one]
      nlinarith [mul_neg_of_pos_of_neg hDR hcn]
  have hsz_eq : ∀ j, ((s * z j : ℤ) : ℝ) = a * w j := by
    intro j
    have hqj : qR j = c * w j := by simpa [Pi.smul_apply, smul_eq_mul] using congr_fun hc j
    simp only [Int.cast_mul, hz_eq j, hqj, a]
    ring
  have hsz_nonneg : ∀ j, 0 ≤ s * z j := by
    intro j
    have hR : (0 : ℝ) ≤ ((s * z j : ℤ) : ℝ) := by
      rw [hsz_eq j]
      exact mul_nonneg (le_of_lt hapos) (hw0 j)
    exact_mod_cast hR
  let d : ι → ℕ := fun j => (s * z j).toNat
  have hd_eq : (fun j => (d j : ℝ)) = a • w := by
    ext j
    have htoNat : ((d j : ℕ) : ℤ) = s * z j := Int.toNat_of_nonneg (hsz_nonneg j)
    have hR : (d j : ℝ) = ((s * z j : ℤ) : ℝ) := by exact_mod_cast htoNat
    simpa [Pi.smul_apply, smul_eq_mul] using hR.trans (hsz_eq j)
  refine ⟨d, ?_, ?_, ?_⟩
  · intro j
    rw [hwS j]
    have hj : (d j : ℝ) = a * w j := by simpa using congr_fun hd_eq j
    constructor
    · intro hwpos
      have hpos : (0 : ℝ) < (d j : ℝ) := by rw [hj]; exact mul_pos hapos hwpos
      exact_mod_cast hpos
    · intro hdpos
      have hpos : (0 : ℝ) < a * w j := by rw [← hj]; exact_mod_cast hdpos
      exact pos_of_mul_pos_right hpos (le_of_lt hapos)
  · rw [hd_eq, Matrix.mulVec_smul, hwker, smul_zero]
  · intro u huS huker
    obtain ⟨c', hc'⟩ := h1 u huS huker
    refine ⟨c' / a, ?_⟩
    rw [hc', hd_eq, smul_smul, div_mul_cancel₀ _ (ne_of_gt hapos)]

private lemma exists_nat_cone_generators {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MQ : Matrix (Fin r) ι ℚ) :
    ∃ d : Finset ι → ι → ℕ,
      (∀ S, MQ.map (Rat.cast : ℚ → ℝ) *ᵥ (fun j => (d S j : ℝ)) = 0) ∧
      (∀ w : ι → ℝ, 0 ≤ w → MQ.map (Rat.cast : ℚ → ℝ) *ᵥ w = 0 →
        ∃ lam : Finset ι → ℝ, (∀ S, 0 ≤ lam S) ∧
          w = ∑ S, lam S • (fun j => (d S j : ℝ))) := by
  let M : Matrix (Fin r) ι ℝ := MQ.map (Rat.cast : ℚ → ℝ)
  let Good (S : Finset ι) : Prop :=
    ∃ d0 : ι → ℕ, (∀ j, j ∈ S ↔ 0 < d0 j) ∧
      M *ᵥ (fun j => (d0 j : ℝ)) = 0 ∧
      (∀ u : ι → ℝ, (∀ j ∉ S, u j = 0) → M *ᵥ u = 0 →
        ∃ c : ℝ, u = c • (fun j => (d0 j : ℝ)))
  classical
  let d : Finset ι → ι → ℕ := fun S => if h : Good S then h.choose else 0
  have hd_ker : ∀ S, M *ᵥ (fun j => (d S j : ℝ)) = 0 := by
    intro S
    by_cases h : Good S
    · simp only [d, dif_pos h]
      exact h.choose_spec.2.1
    · simp only [d, dif_neg h, Pi.zero_apply, Nat.cast_zero]
      exact Matrix.mulVec_zero M
  refine ⟨d, hd_ker, ?_⟩
  have hmain : ∀ k : ℕ, ∀ w : ι → ℝ, 0 ≤ w → M *ᵥ w = 0 →
      (Finset.univ.filter (fun j => w j ≠ 0)).card ≤ k →
      ∃ lam : Finset ι → ℝ, (∀ S, 0 ≤ lam S) ∧
        w = ∑ S, lam S • (fun j => (d S j : ℝ)) := by
    intro k
    induction k with
    | zero =>
      intro w _ _ hcard
      have hemp : Finset.univ.filter (fun j => w j ≠ 0) = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      have hw0 : w = 0 := by
        ext j
        simp only [Pi.zero_apply]
        by_contra hne
        have : j ∈ Finset.univ.filter (fun j => w j ≠ 0) := by simp [hne]
        rw [hemp] at this
        simp at this
      refine ⟨0, fun _ => le_refl 0, ?_⟩
      simp [hw0]
    | succ k ih =>
      intro w hw0 hwker hcard
      let S : Finset ι := Finset.univ.filter (fun j => w j ≠ 0)
      have hScard : S.card ≤ k + 1 := hcard
      have hwS : ∀ j, j ∈ S ↔ 0 < w j := by
        intro j
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => lt_of_le_of_ne (hw0 j) (Ne.symm h), fun h => ne_of_gt h⟩
      by_cases hSne : S.Nonempty
      · by_cases h1 : ∀ u : ι → ℝ, (∀ j ∉ S, u j = 0) → M *ᵥ u = 0 → ∃ c : ℝ, u = c • w
        · have hGood : Good S := exists_nat_ray_of_one_dim MQ S hSne w hw0 hwS hwker h1
          have hspec := hGood.choose_spec
          have hdS_eq : d S = hGood.choose := by simp [d, dif_pos hGood]
          have hwout : ∀ j ∉ S, w j = 0 := by
            intro j hj
            by_contra hne
            exact hj (by simp [S, hne])
          obtain ⟨c, hc⟩ := hspec.2.2 w hwout hwker
          obtain ⟨j₀, hj₀⟩ := hSne
          have hwpos : 0 < w j₀ := (hwS j₀).mp hj₀
          have hdpos : (0 : ℝ) < (hGood.choose j₀ : ℝ) := by
            exact_mod_cast (hspec.1 j₀).mp hj₀
          have hcpos : 0 < c := by
            have hj₀eq : w j₀ = c * (hGood.choose j₀ : ℝ) := by
              simpa [Pi.smul_apply, smul_eq_mul] using congr_fun hc j₀
            rw [hj₀eq] at hwpos
            exact pos_of_mul_pos_left hwpos (le_of_lt hdpos)
          refine ⟨fun T => if T = S then c else 0, ?_, ?_⟩
          · intro T
            dsimp only
            split_ifs
            · exact le_of_lt hcpos
            · exact le_refl 0
          · simp [hdS_eq, hc]
        · push Not at h1
          obtain ⟨u, huout, huker, hnotmul⟩ := h1
          let ratio : ι → ℝ := fun j => u j / w j
          obtain ⟨jmax, hjmaxS, hjmax⟩ := Finset.exists_max_image S ratio hSne
          obtain ⟨jmin, hjminS, hjmin⟩ := Finset.exists_min_image S ratio hSne
          let rmax : ℝ := ratio jmax
          let rmin : ℝ := ratio jmin
          have hlt : rmin < rmax := by
            by_contra hle
            have heq : rmax ≤ rmin := not_lt.mp hle
            apply hnotmul rmin
            ext j
            by_cases hj : j ∈ S
            · have h1' : rmin ≤ ratio j := hjmin j hj
              have h2' : ratio j ≤ rmax := hjmax j hj
              have hr : ratio j = rmin := le_antisymm (h2'.trans heq) h1'
              have hwpos : w j ≠ 0 := ne_of_gt ((hwS j).mp hj)
              simp only [Pi.smul_apply, smul_eq_mul]
              rw [← hr]
              exact (div_mul_cancel₀ (u j) hwpos).symm
            · have hwj : w j = 0 := by
                by_contra hne
                exact hj (by simp [S, hne])
              simp [huout j hj, hwj]
          let w1 : ι → ℝ := rmax • w - u
          let w2 : ι → ℝ := u - rmin • w
          have hw1_nonneg : 0 ≤ w1 := by
            intro j
            simp only [w1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            by_cases hj : j ∈ S
            · have hwpos : 0 < w j := (hwS j).mp hj
              have hr : u j / w j ≤ rmax := hjmax j hj
              have := (div_le_iff₀ hwpos).mp hr
              linarith
            · have hwj : w j = 0 := by by_contra hne; exact hj (by simp [S, hne])
              simp [huout j hj, hwj]
          have hw2_nonneg : 0 ≤ w2 := by
            intro j
            simp only [w2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            by_cases hj : j ∈ S
            · have hwpos : 0 < w j := (hwS j).mp hj
              have hr : rmin ≤ u j / w j := hjmin j hj
              have := (le_div_iff₀ hwpos).mp hr
              linarith
            · have hwj : w j = 0 := by by_contra hne; exact hj (by simp [S, hne])
              simp [huout j hj, hwj]
          have hw1_ker : M *ᵥ w1 = 0 := by
            simp [w1, Matrix.mulVec_sub, Matrix.mulVec_smul, hwker, huker]
          have hw2_ker : M *ᵥ w2 = 0 := by
            simp [w2, Matrix.mulVec_sub, Matrix.mulVec_smul, hwker, huker]
          have hw1_sub : Finset.univ.filter (fun j => w1 j ≠ 0) ⊆ S.erase jmax := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hjeq
              apply hj
              rw [hjeq]
              have hwpos : w jmax ≠ 0 := ne_of_gt ((hwS jmax).mp hjmaxS)
              simp only [w1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rmax, ratio]
              rw [div_mul_cancel₀ _ hwpos, sub_self]
            · by_contra hnotS
              apply hj
              have hwj : w j = 0 := by by_contra hne; exact hnotS (by simp [S, hne])
              simp [w1, huout j hnotS, hwj]
          have hw2_sub : Finset.univ.filter (fun j => w2 j ≠ 0) ⊆ S.erase jmin := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hjeq
              apply hj
              rw [hjeq]
              have hwpos : w jmin ≠ 0 := ne_of_gt ((hwS jmin).mp hjminS)
              simp only [w2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rmin, ratio]
              rw [div_mul_cancel₀ _ hwpos, sub_self]
            · by_contra hnotS
              apply hj
              have hwj : w j = 0 := by by_contra hne; exact hnotS (by simp [S, hne])
              simp [w2, huout j hnotS, hwj]
          have hcard1 : (Finset.univ.filter (fun j => w1 j ≠ 0)).card ≤ k := by
            have h1' := Finset.card_le_card hw1_sub
            rw [Finset.card_erase_of_mem hjmaxS] at h1'
            omega
          have hcard2 : (Finset.univ.filter (fun j => w2 j ≠ 0)).card ≤ k := by
            have h2' := Finset.card_le_card hw2_sub
            rw [Finset.card_erase_of_mem hjminS] at h2'
            omega
          obtain ⟨lam1, hlam1_nn, hw1_eq⟩ := ih w1 hw1_nonneg hw1_ker hcard1
          obtain ⟨lam2, hlam2_nn, hw2_eq⟩ := ih w2 hw2_nonneg hw2_ker hcard2
          have hdiff_pos : 0 < rmax - rmin := sub_pos.mpr hlt
          refine ⟨fun T => (rmax - rmin)⁻¹ * (lam1 T + lam2 T), ?_, ?_⟩
          · intro T
            exact mul_nonneg (inv_nonneg.mpr (le_of_lt hdiff_pos))
              (add_nonneg (hlam1_nn T) (hlam2_nn T))
          · have hcomb : w = (rmax - rmin)⁻¹ • (w1 + w2) := by
              ext j
              simp only [w1, w2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              have hne : rmax - rmin ≠ 0 := ne_of_gt hdiff_pos
              field_simp [hne]
              ring
            rw [hcomb, hw1_eq, hw2_eq, ← Finset.sum_add_distrib, Finset.smul_sum]
            refine Finset.sum_congr rfl fun T _ => ?_
            rw [← add_smul, smul_smul]
      · rw [Finset.not_nonempty_iff_eq_empty] at hSne
        have hw0' : w = 0 := by
          ext j
          simp only [Pi.zero_apply]
          by_contra hne
          have : j ∈ S := by simp [S, hne]
          rw [hSne] at this
          simp at this
        refine ⟨0, fun _ => le_refl 0, ?_⟩
        simp [hw0']
  intro w hw0 hwker
  exact hmain (Fintype.card ι) w hw0 hwker (Finset.card_filter_le _ _)

/-! ### Step 2: Basic feasible solution + recession cone decomposition with linear norm bound -/

private lemma exists_basic_cone_decomp {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix (Fin r) ι ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ z : ι → ℝ, 0 ≤ z →
        ∃ v w : ι → ℝ,
          z = v + w ∧
          0 ≤ v ∧ M *ᵥ v = M *ᵥ z ∧ ‖v‖ ≤ C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖ ∧
          0 ≤ w ∧ M *ᵥ w = 0 := by
  let fS (S : Finset ι) : (S → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin r) :=
    { toFun := fun u => WithLp.toLp 2 (fun i => ∑ j : S, M i j.1 * u j)
      map_add' := fun u₁ u₂ => by
        ext i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        ext i
        simp [Finset.mul_sum, mul_left_comm] }
  classical
  let cS (S : Finset ι) : ℝ :=
    if h : LinearMap.ker (fS S) = ⊥ then
      ‖((fS S).exists_leftInverse_of_injective h).choose.toContinuousLinearMap‖
    else 0
  have hcS_nn : ∀ S, 0 ≤ cS S := by
    intro S
    by_cases h : LinearMap.ker (fS S) = ⊥
    · simp only [cS, dif_pos h]
      exact norm_nonneg _
    · simp [cS, dif_neg h]
  let C₀ : ℝ := ∑ S : Finset ι, cS S
  have hC₀_nn : 0 ≤ C₀ := Finset.sum_nonneg (fun S _ => hcS_nn S)
  have hnorm_of_indep : ∀ (S : Finset ι) (z : ι → ℝ),
      LinearMap.ker (fS S) = ⊥ → (∀ j ∉ S, z j = 0) →
      ‖z‖ ≤ C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖ := by
    intro S z hker hzout
    let zS : S → ℝ := fun j => z j.1
    have hfS_eq : fS S zS = WithLp.toLp 2 (M *ᵥ z) := by
      ext i
      simp only [fS, LinearMap.coe_mk, AddHom.coe_mk, mulVec, dotProduct, zS]
      calc ∑ j : S, M i j.1 * z j.1
          = ∑ j ∈ S, M i j * z j := by
            rw [← Finset.sum_attach S (fun j => M i j * z j)]
            rfl
        _ = ∑ j : ι, M i j * z j := by
            apply Finset.sum_subset (Finset.subset_univ S)
            intro j _ hj
            simp [hzout j hj]
    let g := ((fS S).exists_leftInverse_of_injective hker).choose
    have hg : g.comp (fS S) = LinearMap.id :=
      ((fS S).exists_leftInverse_of_injective hker).choose_spec
    have hgz : g (fS S zS) = zS := by
      simpa using LinearMap.congr_fun hg zS
    have hnorm_zS : ‖zS‖ ≤ cS S * ‖WithLp.toLp 2 (M *ᵥ z)‖ := by
      rw [← hfS_eq]
      calc ‖zS‖ = ‖g (fS S zS)‖ := by rw [hgz]
        _ = ‖g.toContinuousLinearMap (fS S zS)‖ := rfl
        _ ≤ ‖g.toContinuousLinearMap‖ * ‖fS S zS‖ := g.toContinuousLinearMap.le_opNorm _
        _ = cS S * ‖fS S zS‖ := by simp [cS, dif_pos hker, g]
    have hnorm_z : ‖z‖ ≤ ‖zS‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg zS)]
      intro j
      by_cases hj : j ∈ S
      · exact norm_le_pi_norm zS ⟨j, hj⟩
      · simp [hzout j hj]
    have hcS_le : cS S ≤ C₀ := Finset.single_le_sum (fun T _ => hcS_nn T) (Finset.mem_univ S)
    exact hnorm_z.trans (hnorm_zS.trans (mul_le_mul_of_nonneg_right hcS_le (norm_nonneg _)))
  refine ⟨C₀, hC₀_nn, ?_⟩
  have hmain : ∀ k : ℕ, ∀ z : ι → ℝ, 0 ≤ z →
      (Finset.univ.filter (fun j => z j ≠ 0)).card ≤ k →
      ∃ v w : ι → ℝ,
        z = v + w ∧
        0 ≤ v ∧ M *ᵥ v = M *ᵥ z ∧ ‖v‖ ≤ C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖ ∧
        0 ≤ w ∧ M *ᵥ w = 0 := by
    intro k
    induction k with
    | zero =>
      intro z _ hcard
      have hemp : Finset.univ.filter (fun j => z j ≠ 0) = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      have hz0 : z = 0 := by
        ext j
        simp only [Pi.zero_apply]
        by_contra hne
        have : j ∈ Finset.univ.filter (fun j => z j ≠ 0) := by simp [hne]
        rw [hemp] at this
        simp at this
      refine ⟨0, 0, by simp [hz0], le_refl 0, by simp [hz0], ?_, le_refl 0, by simp⟩
      simp [hz0]
    | succ k ih =>
      intro z hz0 hcard
      let S : Finset ι := Finset.univ.filter (fun j => z j ≠ 0)
      have hScard : S.card ≤ k + 1 := hcard
      have hzS : ∀ j, j ∈ S ↔ 0 < z j := by
        intro j
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => lt_of_le_of_ne (hz0 j) (Ne.symm h), fun h => ne_of_gt h⟩
      have hzout : ∀ j ∉ S, z j = 0 := by
        intro j hj
        by_contra hne
        exact hj (by simp [S, hne])
      by_cases hker : LinearMap.ker (fS S) = ⊥
      · exact ⟨z, 0, by simp, hz0, rfl, hnorm_of_indep S z hker hzout, le_refl 0, by simp⟩
      · have hker' : LinearMap.ker (fS S) ≠ ⊥ := hker
        rw [Submodule.ne_bot_iff] at hker'
        obtain ⟨δS, hδSker, hδSne⟩ := hker'
        rw [LinearMap.mem_ker] at hδSker
        let δ₀ : ι → ℝ := fun j => if h : j ∈ S then δS ⟨j, h⟩ else 0
        have hδ₀ne : δ₀ ≠ 0 := by
          intro h0
          apply hδSne
          ext ⟨j, hj⟩
          simpa [δ₀, hj] using congr_fun h0 j
        have hδ₀out : ∀ j ∉ S, δ₀ j = 0 := fun j hj => by simp [δ₀, hj]
        have hδ₀ker : M *ᵥ δ₀ = 0 := by
          ext i
          have hi : (fS S δS).ofLp i = 0 := by rw [hδSker]; rfl
          simp only [fS, LinearMap.coe_mk, AddHom.coe_mk] at hi
          simp only [mulVec, dotProduct, Pi.zero_apply]
          rw [← hi]
          calc ∑ j : ι, M i j * δ₀ j
              = ∑ j ∈ S, M i j * δ₀ j := by
                symm
                apply Finset.sum_subset (Finset.subset_univ S)
                intro j _ hj
                simp [hδ₀out j hj]
            _ = ∑ j ∈ S.attach, M i j.1 * δS j := by
                rw [← Finset.sum_attach S]
                refine Finset.sum_congr rfl fun j _ => ?_
                simp [δ₀, j.2]
            _ = ∑ j : S, M i j.1 * δS j := rfl
        -- Choose sign of δ so some coordinate in S is positive
        have hpos_ex : ∃ δ : ι → ℝ, (∀ j ∉ S, δ j = 0) ∧ M *ᵥ δ = 0 ∧ ∃ j ∈ S, 0 < δ j := by
          by_cases hpos : ∃ j ∈ S, 0 < δ₀ j
          · exact ⟨δ₀, hδ₀out, hδ₀ker, hpos⟩
          · push Not at hpos
            have hneg : ∃ j ∈ S, δ₀ j < 0 := by
              by_contra hall
              push Not at hall
              apply hδ₀ne
              ext j
              simp only [Pi.zero_apply]
              by_cases hj : j ∈ S
              · exact le_antisymm (hpos j hj) (hall j hj)
              · exact hδ₀out j hj
            obtain ⟨j, hjS, hjlt⟩ := hneg
            exact ⟨-δ₀, fun j' hj' => by simp [hδ₀out j' hj'],
              by simp [Matrix.mulVec_neg, hδ₀ker], j, hjS, neg_pos.mpr hjlt⟩
        obtain ⟨δ, hδout, hδker, jpos, hjposS, hjpos⟩ := hpos_ex
        have hSne : S.Nonempty := ⟨jpos, hjposS⟩
        let ratio : ι → ℝ := fun j => δ j / z j
        obtain ⟨jmax, hjmaxS, hjmax⟩ := Finset.exists_max_image S ratio hSne
        obtain ⟨jmin, hjminS, hjmin⟩ := Finset.exists_min_image S ratio hSne
        let rmax : ℝ := ratio jmax
        let rmin : ℝ := ratio jmin
        have hrmax_pos : 0 < rmax :=
          lt_of_lt_of_le (div_pos hjpos ((hzS jpos).mp hjposS)) (hjmax jpos hjposS)
        by_cases hrmin_nn : 0 ≤ rmin
        · -- Subcase 2a: δ ≥ 0, peel off recession ray rmax⁻¹ • δ
          let w0 : ι → ℝ := rmax⁻¹ • δ
          let z' : ι → ℝ := z - w0
          have hw0_nn : 0 ≤ w0 := by
            intro j
            simp only [w0, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            by_cases hj : j ∈ S
            · have hzpos : 0 < z j := (hzS j).mp hj
              have hδj : 0 ≤ δ j := by
                have := le_trans hrmin_nn (hjmin j hj)
                exact (le_div_iff₀ hzpos).mp this |> fun h => by linarith
              exact mul_nonneg (inv_nonneg.mpr (le_of_lt hrmax_pos)) hδj
            · simp [hδout j hj]
          have hw0_ker : M *ᵥ w0 = 0 := by simp [w0, Matrix.mulVec_smul, hδker]
          have hz'_nn : 0 ≤ z' := by
            intro j
            simp only [z', w0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            by_cases hj : j ∈ S
            · have hzpos : 0 < z j := (hzS j).mp hj
              have hr : δ j / z j ≤ rmax := hjmax j hj
              have hδle : δ j ≤ rmax * z j := (div_le_iff₀ hzpos).mp hr
              have hmul : rmax⁻¹ * δ j ≤ z j := by
                have := mul_le_mul_of_nonneg_left hδle (inv_nonneg.mpr (le_of_lt hrmax_pos))
                rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hrmax_pos), one_mul] at this
              linarith
            · simp [hzout j hj, hδout j hj]
          have hz'_mul : M *ᵥ z' = M *ᵥ z := by
            simp [z', Matrix.mulVec_sub, hw0_ker]
          have hz'_sub : Finset.univ.filter (fun j => z' j ≠ 0) ⊆ S.erase jmax := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hjeq
              apply hj
              rw [hjeq]
              have hzne : z jmax ≠ 0 := ne_of_gt ((hzS jmax).mp hjmaxS)
              have hδne : δ jmax ≠ 0 := by
                intro h0
                simp only [rmax, ratio, h0, zero_div] at hrmax_pos
                exact lt_irrefl 0 hrmax_pos
              simp only [z', w0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rmax, ratio]
              field_simp [hzne, hδne]
              ring
            · by_contra hnotS
              apply hj
              simp [z', w0, hzout j hnotS, hδout j hnotS]
          have hcard' : (Finset.univ.filter (fun j => z' j ≠ 0)).card ≤ k := by
            have h1 := Finset.card_le_card hz'_sub
            rw [Finset.card_erase_of_mem hjmaxS] at h1
            omega
          obtain ⟨v, w', hz'_eq, hv_nn, hv_mul, hv_norm, hw'_nn, hw'_ker⟩ := ih z' hz'_nn hcard'
          refine ⟨v, w' + w0, ?_, hv_nn, hv_mul.trans hz'_mul, ?_,
            add_nonneg hw'_nn hw0_nn, by simp [Matrix.mulVec_add, hw'_ker, hw0_ker]⟩
          · rw [← add_assoc, ← hz'_eq]
            simp [z']
          · rwa [hz'_mul] at hv_norm
        · -- Subcase 2b: rmin < 0 < rmax, express z as convex combination of z1, z2
          have hrmin_neg : rmin < 0 := not_le.mp hrmin_nn
          let z1 : ι → ℝ := z - rmax⁻¹ • δ
          let z2 : ι → ℝ := z - rmin⁻¹ • δ
          have hz1_nn : 0 ≤ z1 := by
            intro j
            simp only [z1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            by_cases hj : j ∈ S
            · have hzpos : 0 < z j := (hzS j).mp hj
              have hδle : δ j ≤ rmax * z j := (div_le_iff₀ hzpos).mp (hjmax j hj)
              have hmul : rmax⁻¹ * δ j ≤ z j := by
                have := mul_le_mul_of_nonneg_left hδle (inv_nonneg.mpr (le_of_lt hrmax_pos))
                rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hrmax_pos), one_mul] at this
              linarith
            · simp [hzout j hj, hδout j hj]
          have hz2_nn : 0 ≤ z2 := by
            intro j
            simp only [z2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            by_cases hj : j ∈ S
            · have hzpos : 0 < z j := (hzS j).mp hj
              have hδge : rmin * z j ≤ δ j := (le_div_iff₀ hzpos).mp (hjmin j hj)
              have hmul : rmin⁻¹ * δ j ≤ z j := by
                have := mul_le_mul_of_nonpos_left hδge (inv_nonpos.mpr (le_of_lt hrmin_neg))
                rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_lt hrmin_neg), one_mul] at this
              linarith
            · simp [hzout j hj, hδout j hj]
          have hz1_mul : M *ᵥ z1 = M *ᵥ z := by
            simp [z1, Matrix.mulVec_sub, Matrix.mulVec_smul, hδker]
          have hz2_mul : M *ᵥ z2 = M *ᵥ z := by
            simp [z2, Matrix.mulVec_sub, Matrix.mulVec_smul, hδker]
          have hz1_sub : Finset.univ.filter (fun j => z1 j ≠ 0) ⊆ S.erase jmax := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hjeq
              apply hj
              rw [hjeq]
              have hzne : z jmax ≠ 0 := ne_of_gt ((hzS jmax).mp hjmaxS)
              have hδne : δ jmax ≠ 0 := by
                intro h0
                simp only [rmax, ratio, h0, zero_div] at hrmax_pos
                exact lt_irrefl 0 hrmax_pos
              simp only [z1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rmax, ratio]
              field_simp [hzne, hδne]
              ring
            · by_contra hnotS
              apply hj
              simp [z1, hzout j hnotS, hδout j hnotS]
          have hz2_sub : Finset.univ.filter (fun j => z2 j ≠ 0) ⊆ S.erase jmin := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · intro hjeq
              apply hj
              rw [hjeq]
              have hzne : z jmin ≠ 0 := ne_of_gt ((hzS jmin).mp hjminS)
              have hδne : δ jmin ≠ 0 := by
                intro h0
                simp only [rmin, ratio, h0, zero_div] at hrmin_neg
                exact lt_irrefl 0 hrmin_neg
              simp only [z2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rmin, ratio]
              field_simp [hzne, hδne]
              ring
            · by_contra hnotS
              apply hj
              simp [z2, hzout j hnotS, hδout j hnotS]
          have hcard1 : (Finset.univ.filter (fun j => z1 j ≠ 0)).card ≤ k := by
            have h1 := Finset.card_le_card hz1_sub
            rw [Finset.card_erase_of_mem hjmaxS] at h1
            omega
          have hcard2 : (Finset.univ.filter (fun j => z2 j ≠ 0)).card ≤ k := by
            have h2 := Finset.card_le_card hz2_sub
            rw [Finset.card_erase_of_mem hjminS] at h2
            omega
          obtain ⟨v1, w1, hz1_eq, hv1_nn, hv1_mul, hv1_norm, hw1_nn, hw1_ker⟩ := ih z1 hz1_nn hcard1
          obtain ⟨v2, w2, hz2_eq, hv2_nn, hv2_mul, hv2_norm, hw2_nn, hw2_ker⟩ := ih z2 hz2_nn hcard2
          let θ : ℝ := rmax / (rmax - rmin)
          have hden_pos : 0 < rmax - rmin := by linarith
          have hθ_nn : 0 ≤ θ := div_nonneg (le_of_lt hrmax_pos) (le_of_lt hden_pos)
          have h1θ_nn : 0 ≤ 1 - θ := by
            have : 1 - θ = (-rmin) / (rmax - rmin) := by
              simp only [θ]; field_simp [ne_of_gt hden_pos]; ring
            rw [this]
            exact div_nonneg (by linarith) (le_of_lt hden_pos)
          have hz_conv : z = θ • z1 + (1 - θ) • z2 := by
            ext j
            simp only [z1, z2, θ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            have h1 : rmax ≠ 0 := ne_of_gt hrmax_pos
            have h2 : rmin ≠ 0 := ne_of_lt hrmin_neg
            have h3 : rmax - rmin ≠ 0 := ne_of_gt hden_pos
            field_simp [h1, h2, h3]
            ring
          refine ⟨θ • v1 + (1 - θ) • v2, θ • w1 + (1 - θ) • w2, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hz_conv, hz1_eq, hz2_eq, smul_add, smul_add]
            abel
          · exact add_nonneg (smul_nonneg hθ_nn hv1_nn) (smul_nonneg h1θ_nn hv2_nn)
          · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
              hv1_mul, hv2_mul, hz1_mul, hz2_mul, ← add_smul]
            simp
          · rw [hz1_mul] at hv1_norm
            rw [hz2_mul] at hv2_norm
            calc ‖θ • v1 + (1 - θ) • v2‖
                ≤ ‖θ • v1‖ + ‖(1 - θ) • v2‖ := norm_add_le _ _
              _ = θ * ‖v1‖ + (1 - θ) * ‖v2‖ := by
                rw [norm_smul, norm_smul, Real.norm_of_nonneg hθ_nn, Real.norm_of_nonneg h1θ_nn]
              _ ≤ θ * (C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖) + (1 - θ) * (C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖) :=
                add_le_add (mul_le_mul_of_nonneg_left hv1_norm hθ_nn)
                  (mul_le_mul_of_nonneg_left hv2_norm h1θ_nn)
              _ = C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖ := by ring
          · exact add_nonneg (smul_nonneg hθ_nn hw1_nn) (smul_nonneg h1θ_nn hw2_nn)
          · simp [Matrix.mulVec_add, Matrix.mulVec_smul, hw1_ker, hw2_ker]
  intro z hz0
  exact hmain (Fintype.card ι) z hz0 (Finset.card_filter_le _ _)

/-! ### Step 3: Master bounded integer-ray reduction lemma for rational matrices -/

private lemma exists_bounded_reduction {r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (MQ : Matrix (Fin r) ι ℚ) :
    ∃ (C₀ C₁ : ℝ) (d : Finset ι → ι → ℕ),
      0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      (∀ S, MQ.map (Rat.cast : ℚ → ℝ) *ᵥ (fun j => (d S j : ℝ)) = 0) ∧
      ∀ z : ι → ℝ, 0 ≤ z →
        ∃ (z' : ι → ℝ) (m : Finset ι → ℕ),
          z = z' + ∑ S, (m S : ℝ) • (fun j => (d S j : ℝ)) ∧
          0 ≤ z' ∧
          MQ.map (Rat.cast : ℚ → ℝ) *ᵥ z' = MQ.map (Rat.cast : ℚ → ℝ) *ᵥ z ∧
          ‖z'‖ ≤ C₀ * ‖WithLp.toLp 2 (MQ.map (Rat.cast : ℚ → ℝ) *ᵥ z)‖ + C₁ := by
  let M : Matrix (Fin r) ι ℝ := MQ.map (Rat.cast : ℚ → ℝ)
  obtain ⟨C₀, hC₀_nn, hdecomp⟩ := exists_basic_cone_decomp M
  obtain ⟨d, hd_ker, hcone⟩ := exists_nat_cone_generators MQ
  let C₁ : ℝ := ∑ S : Finset ι, ‖(fun j => (d S j : ℝ))‖
  have hC₁_nn : 0 ≤ C₁ := Finset.sum_nonneg (fun S _ => norm_nonneg _)
  refine ⟨C₀, C₁, d, hC₀_nn, hC₁_nn, hd_ker, ?_⟩
  intro z hz0
  obtain ⟨v, w, hz_eq, hv_nn, hv_mul, hv_norm, hw_nn, hw_ker⟩ := hdecomp z hz0
  obtain ⟨lam, hlam_nn, hw_eq⟩ := hcone w hw_nn hw_ker
  let m : Finset ι → ℕ := fun S => Nat.floor (lam S)
  let θ : Finset ι → ℝ := fun S => lam S - (m S : ℝ)
  have hθ_nn : ∀ S, 0 ≤ θ S := fun S => sub_nonneg.mpr (Nat.floor_le (hlam_nn S))
  have hθ_le : ∀ S, θ S ≤ 1 := fun S => by
    have hlt := Nat.lt_floor_add_one (lam S)
    linarith
  let z' : ι → ℝ := v + ∑ S, θ S • (fun j => (d S j : ℝ))
  refine ⟨z', m, ?_, ?_, ?_, ?_⟩
  · rw [hz_eq, hw_eq]
    simp only [z', add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← add_smul]
    simp [θ]
  · refine add_nonneg hv_nn ?_
    intro j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact Finset.sum_nonneg (fun S _ => mul_nonneg (hθ_nn S) (Nat.cast_nonneg _))
  · change M *ᵥ z' = M *ᵥ z
    simp only [z', Matrix.mulVec_add, hv_mul]
    have hsum_ker : M *ᵥ (∑ S, θ S • (fun j => (d S j : ℝ))) = 0 := by
      have : ∀ (F : Finset (Finset ι)),
          M *ᵥ (∑ S ∈ F, θ S • (fun j => (d S j : ℝ))) = 0 := by
        intro F
        induction F using Finset.induction with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Matrix.mulVec_add, Matrix.mulVec_smul, hd_ker a,
            smul_zero, zero_add, ih]
      exact this Finset.univ
    rw [hsum_ker, add_zero]
  · calc ‖z'‖
        ≤ ‖v‖ + ‖∑ S, θ S • (fun j => (d S j : ℝ))‖ := norm_add_le _ _
      _ ≤ C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖ + ∑ S, ‖θ S • (fun j => (d S j : ℝ))‖ :=
          add_le_add hv_norm (norm_sum_le _ _)
      _ ≤ C₀ * ‖WithLp.toLp 2 (M *ᵥ z)‖ + C₁ := by
          refine add_le_add (le_refl _) (Finset.sum_le_sum fun S _ => ?_)
          rw [norm_smul, Real.norm_of_nonneg (hθ_nn S)]
          exact mul_le_of_le_one_left (norm_nonneg _) (hθ_le S)

/-! ### Step 4: Helpers specific to `Recourse` -/

private lemma phi_le_of_feasible {r mh mb : ℕ} (R : Recourse r mh mb)
    {t : EuclideanSpace ℝ (Fin r)} (y : Fin mh → ℕ) (yb : Fin mb → ℝ)
    (hyb : 0 ≤ yb) (heq : WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)) + R.Wb *ᵥ yb) = t) :
    R.Phi t ≤ ((R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb : ℝ) : EReal) := by
  unfold Recourse.Phi
  exact (iInf_le _ y).trans <| (iInf_le _ yb).trans <| (iInf_le _ hyb).trans (iInf_le _ heq)

private lemma exists_feasible_lt_of_phi_lt {r mh mb : ℕ} (R : Recourse r mh mb)
    {t : EuclideanSpace ℝ (Fin r)} {b : ℝ} (h : R.Phi t < (b : EReal)) :
    ∃ (y : Fin mh → ℕ) (yb : Fin mb → ℝ),
      0 ≤ yb ∧
      WithLp.toLp 2 (R.W *ᵥ (fun i => (y i : ℝ)) + R.Wb *ᵥ yb) = t ∧
      R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb < b := by
  unfold Recourse.Phi at h
  rw [iInf_lt_iff] at h
  obtain ⟨y, h⟩ := h
  rw [iInf_lt_iff] at h
  obtain ⟨yb, h⟩ := h
  rw [iInf_lt_iff] at h
  obtain ⟨hyb, h⟩ := h
  rw [iInf_lt_iff] at h
  obtain ⟨heq, hlt⟩ := h
  exact ⟨y, yb, hyb, heq, EReal.coe_lt_coe_iff.mp hlt⟩

private lemma phi_ne_top_and_ne_bot {r mh mb : ℕ} (R : Recourse r mh mb) (hB3 : R.B3) :
    ∀ t ∈ R.Tset, R.Phi t ≠ ⊤ ∧ R.Phi t ≠ ⊥ := by
  obtain ⟨u, huW, huWb⟩ := hB3
  intro t ht
  obtain ⟨y, yb, hyb, heq⟩ := ht
  constructor
  · have hle := phi_le_of_feasible R y yb hyb heq
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle
  · have hlb : ((u ⬝ᵥ t.ofLp : ℝ) : EReal) ≤ R.Phi t := by
      unfold Recourse.Phi
      refine le_iInf fun y' => le_iInf fun yb' => le_iInf fun hyb' => le_iInf fun heq' => ?_
      rw [EReal.coe_le_coe_iff]
      have h1 : (R.Wᵀ *ᵥ u) ⬝ᵥ (fun i => (y' i : ℝ)) ≤ R.q ⬝ᵥ (fun i => (y' i : ℝ)) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (huW i) (Nat.cast_nonneg _)
      have h2 : (R.Wbᵀ *ᵥ u) ⬝ᵥ yb' ≤ R.qb ⬝ᵥ yb' :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (huWb i) (hyb' i)
      have h3 : u ⬝ᵥ t.ofLp =
          (R.Wᵀ *ᵥ u) ⬝ᵥ (fun i => (y' i : ℝ)) + (R.Wbᵀ *ᵥ u) ⬝ᵥ yb' := by
        have ht' : t.ofLp = R.W *ᵥ (fun i => (y' i : ℝ)) + R.Wb *ᵥ yb' := by
          simpa using congr_arg WithLp.ofLp heq'.symm
        rw [ht', dotProduct_add, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
          ← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose]
      linarith
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlb

/-- Construct the rational block matrix `[W | Wb]` over `Fin mh ⊕ Fin mb` from `R.B1`. -/
private noncomputable def recourseRatMatrix {r mh mb : ℕ} (R : Recourse r mh mb) (hB1 : R.B1) :
    Matrix (Fin r) (Fin mh ⊕ Fin mb) ℚ :=
  fun i j => match j with
    | Sum.inl j₁ => (hB1.1 i j₁).choose
    | Sum.inr j₂ => (hB1.2 i j₂).choose

private lemma recourseRatMatrix_map {r mh mb : ℕ} (R : Recourse r mh mb) (hB1 : R.B1) :
    (recourseRatMatrix R hB1).map (Rat.cast : ℚ → ℝ) =
      fun i j => match j with
        | Sum.inl j₁ => R.W i j₁
        | Sum.inr j₂ => R.Wb i j₂ := by
  ext i j
  rw [Matrix.map_apply]
  cases j with
  | inl j₁ => exact (hB1.1 i j₁).choose_spec.symm
  | inr j₂ => exact (hB1.2 i j₂).choose_spec.symm

private lemma block_mulVec_elim {r mh mb : ℕ} (R : Recourse r mh mb) (hB1 : R.B1)
    (y : Fin mh → ℝ) (yb : Fin mb → ℝ) :
    (recourseRatMatrix R hB1).map (Rat.cast : ℚ → ℝ) *ᵥ Sum.elim y yb =
      R.W *ᵥ y + R.Wb *ᵥ yb := by
  ext i
  rw [recourseRatMatrix_map]
  simp [mulVec, dotProduct, Fintype.sum_sum_type]

private lemma phi_lowerSemicontinuousOn {r mh mb : ℕ} (R : Recourse r mh mb)
    (hB1 : R.B1) (hB3 : R.B3) :
    LowerSemicontinuousOn R.Phi R.Tset := by
  have hfin := phi_ne_top_and_ne_bot R hB3
  obtain ⟨u, huW, huWb⟩ := hB3
  let MQ := recourseRatMatrix R hB1
  let M := MQ.map (Rat.cast : ℚ → ℝ)
  obtain ⟨C₀, C₁, d, hC₀_nn, hC₁_nn, hd_ker, hred⟩ := exists_bounded_reduction MQ
  -- Every integer kernel ray has nonnegative cost under (q, qb) by dual feasibility (B3)
  have hd_cost_nn : ∀ S, 0 ≤ Sum.elim R.q R.qb ⬝ᵥ (fun j => (d S j : ℝ)) := by
    intro S
    let c : Fin mh ⊕ Fin mb → ℝ := Sum.elim R.q R.qb
    have hdu : ∀ j, (Mᵀ *ᵥ u) j ≤ c j := by
      intro j
      cases j with
      | inl j₁ =>
        have : (Mᵀ *ᵥ u) (Sum.inl j₁) = (R.Wᵀ *ᵥ u) j₁ := by
          simp only [M, MQ, recourseRatMatrix_map, mulVec, dotProduct]
          rfl
        simpa [c, this] using huW j₁
      | inr j₂ =>
        have : (Mᵀ *ᵥ u) (Sum.inr j₂) = (R.Wbᵀ *ᵥ u) j₂ := by
          simp only [M, MQ, recourseRatMatrix_map, mulVec, dotProduct]
          rfl
        simpa [c, this] using huWb j₂
    have h1 : (Mᵀ *ᵥ u) ⬝ᵥ (fun j => (d S j : ℝ)) ≤ c ⬝ᵥ (fun j => (d S j : ℝ)) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hdu j) (Nat.cast_nonneg _)
    have h2 : (Mᵀ *ᵥ u) ⬝ᵥ (fun j => (d S j : ℝ)) = 0 := by
      rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.transpose_transpose]
      change u ⬝ᵥ (MQ.map (Rat.cast : ℚ → ℝ) *ᵥ (fun j => (d S j : ℝ))) = 0
      rw [hd_ker S, dotProduct_zero]
    linarith
  -- Bounded near-optimal feasible solution helper
  have hbounded_feas : ∀ (t : EuclideanSpace ℝ (Fin r)) (b : ℝ),
      R.Phi t < (b : EReal) →
      ∃ (y' : Fin mh → ℕ) (yb' : Fin mb → ℝ),
        0 ≤ yb' ∧
        WithLp.toLp 2 (R.W *ᵥ (fun i => (y' i : ℝ)) + R.Wb *ᵥ yb') = t ∧
        R.q ⬝ᵥ (fun i => (y' i : ℝ)) + R.qb ⬝ᵥ yb' < b ∧
        (∀ i, (y' i : ℝ) ≤ C₀ * ‖t‖ + C₁) ∧
        ‖yb'‖ ≤ C₀ * ‖t‖ + C₁ := by
    intro t b hlt
    obtain ⟨y, yb, hyb, heq, hcost⟩ := exists_feasible_lt_of_phi_lt R hlt
    let z : Fin mh ⊕ Fin mb → ℝ := Sum.elim (fun i => (y i : ℝ)) yb
    have hz_nn : 0 ≤ z := by
      intro j; cases j with
      | inl i => exact Nat.cast_nonneg _
      | inr i => exact hyb i
    have hMz : M *ᵥ z = t.ofLp := by
      change (recourseRatMatrix R hB1).map (Rat.cast : ℚ → ℝ) *ᵥ Sum.elim (fun i => (y i : ℝ)) yb = t.ofLp
      rw [block_mulVec_elim]
      simpa using congr_arg WithLp.ofLp heq
    obtain ⟨z', m, hz_eq, hz'_nn, hMz', hz'_norm⟩ := hred z hz_nn
    have hy'_nat : ∀ i : Fin mh, ∃ k : ℕ, z' (Sum.inl i) = (k : ℝ) := by
      intro i
      have hi := congr_fun hz_eq (Sum.inl i)
      simp only [z, Sum.elim_inl, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
      let sub : ℕ := ∑ S, m S * d S (Sum.inl i)
      have hsubR : (sub : ℝ) = ∑ S, (m S : ℝ) * (d S (Sum.inl i) : ℝ) := by
        simp [sub]
      have hleR : (sub : ℝ) ≤ (y i : ℝ) := by
        have h0 : 0 ≤ z' (Sum.inl i) := hz'_nn (Sum.inl i)
        linarith
      have hle : sub ≤ y i := Nat.cast_le.mp hleR
      refine ⟨y i - sub, ?_⟩
      rw [Nat.cast_sub hle, hsubR]
      linarith
    choose y' hy'_eq using hy'_nat
    let yb' : Fin mb → ℝ := fun i => z' (Sum.inr i)
    have hz'_elim : z' = Sum.elim (fun i => (y' i : ℝ)) yb' := by
      ext j; cases j with
      | inl i => exact hy'_eq i
      | inr i => rfl
    have hyb'_nn : 0 ≤ yb' := fun i => hz'_nn (Sum.inr i)
    have heq' : WithLp.toLp 2 (R.W *ᵥ (fun i => (y' i : ℝ)) + R.Wb *ᵥ yb') = t := by
      apply WithLp.ofLp_injective 2
      rw [← block_mulVec_elim R hB1, ← hz'_elim]
      exact hMz'.trans hMz
    have hcost' : R.q ⬝ᵥ (fun i => (y' i : ℝ)) + R.qb ⬝ᵥ yb' < b := by
      have hcz : Sum.elim R.q R.qb ⬝ᵥ z = R.q ⬝ᵥ (fun i => (y i : ℝ)) + R.qb ⬝ᵥ yb := by
        simp [z, dotProduct, Fintype.sum_sum_type]
      have hcz' : Sum.elim R.q R.qb ⬝ᵥ z' = R.q ⬝ᵥ (fun i => (y' i : ℝ)) + R.qb ⬝ᵥ yb' := by
        rw [hz'_elim]
        simp [dotProduct, Fintype.sum_sum_type]
      have hdiff : Sum.elim R.q R.qb ⬝ᵥ z =
          Sum.elim R.q R.qb ⬝ᵥ z' +
            ∑ S, (m S : ℝ) * (Sum.elim R.q R.qb ⬝ᵥ (fun j => (d S j : ℝ))) := by
        rw [hz_eq, dotProduct_add, dotProduct_sum]
        congr 1
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
      have hsum_nn : 0 ≤ ∑ S, (m S : ℝ) * (Sum.elim R.q R.qb ⬝ᵥ (fun j => (d S j : ℝ))) :=
        Finset.sum_nonneg fun S _ => mul_nonneg (Nat.cast_nonneg _) (hd_cost_nn S)
      linarith
    have hnorm_t : ‖z'‖ ≤ C₀ * ‖t‖ + C₁ := by
      have hMz' : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ z = t.ofLp := hMz
      simpa [hMz'] using hz'_norm
    refine ⟨y', yb', hyb'_nn, heq', hcost', ?_, ?_⟩
    · intro i
      have h1 : (y' i : ℝ) ≤ ‖z' (Sum.inl i)‖ := by
        rw [← hy'_eq i, Real.norm_of_nonneg (hz'_nn (Sum.inl i))]
      exact h1.trans ((norm_le_pi_norm z' (Sum.inl i)).trans hnorm_t)
    · rw [pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg hC₀_nn (norm_nonneg t)) hC₁_nn)]
      intro i
      exact (norm_le_pi_norm z' (Sum.inr i)).trans hnorm_t
  -- Now prove LowerSemicontinuousOn
  intro t ht a ha
  obtain ⟨b, hab, hbt⟩ := EReal.exists_between_coe_real ha
  by_contra hnot
  have hseq : ∀ n : ℕ, ∃ t' ∈ R.Tset, dist t' t < 1 / ((n : ℝ) + 1) ∧ R.Phi t' ≤ a := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    by_contra hall
    push Not at hall
    apply hnot
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]
    exact ⟨1 / ((n : ℝ) + 1), hpos, fun t' ⟨hball, ht'T⟩ => hall t' ht'T (Metric.mem_ball.mp hball)⟩
  choose tn htnT htndist htnle using hseq
  have htn_lt_b : ∀ n, R.Phi (tn n) < (b : EReal) :=
    fun n => lt_of_le_of_lt (htnle n) hab
  have hsol : ∀ n, ∃ p : (Fin mh → ℕ) × (Fin mb → ℝ),
      0 ≤ p.2 ∧
      WithLp.toLp 2 (R.W *ᵥ (fun i => (p.1 i : ℝ)) + R.Wb *ᵥ p.2) = tn n ∧
      R.q ⬝ᵥ (fun i => (p.1 i : ℝ)) + R.qb ⬝ᵥ p.2 < b ∧
      (∀ i, (p.1 i : ℝ) ≤ C₀ * ‖tn n‖ + C₁) ∧
      ‖p.2‖ ≤ C₀ * ‖tn n‖ + C₁ := by
    intro n
    obtain ⟨y', yb', h1, h2, h3, h4, h5⟩ := hbounded_feas (tn n) b (htn_lt_b n)
    exact ⟨(y', yb'), h1, h2, h3, h4, h5⟩
  choose pn hpn_nn hpn_eq hpn_cost hpn_y hpn_yb using hsol
  -- Uniform bound on tn
  let B : ℝ := C₀ * (‖t‖ + 1) + C₁
  have htn_norm : ∀ n, ‖tn n‖ ≤ ‖t‖ + 1 := by
    intro n
    have h1 : dist (tn n) t < 1 := by
      refine (htndist n).trans_le ?_
      rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      linarith
    have h2 : ‖tn n - t‖ < 1 := by rwa [dist_eq_norm] at h1
    calc ‖tn n‖ = ‖(tn n - t) + t‖ := by abel_nf
      _ ≤ ‖tn n - t‖ + ‖t‖ := norm_add_le _ _
      _ ≤ 1 + ‖t‖ := by linarith
      _ = ‖t‖ + 1 := add_comm _ _
  have hbound_n : ∀ n, C₀ * ‖tn n‖ + C₁ ≤ B :=
    fun n => add_le_add (mul_le_mul_of_nonneg_left (htn_norm n) hC₀_nn) (le_refl C₁)
  -- Compactness in (Fin mh → ℕ) × (Fin mb → ℝ)
  let Nbound : ℕ := Nat.floor B
  let Ky : Set (Fin mh → ℕ) := {y | ∀ i, y i ≤ Nbound}
  let Kyb : Set (Fin mb → ℝ) := Metric.closedBall (0 : Fin mb → ℝ) B ∩ {yb | 0 ≤ yb}
  have hKy_fin : Ky.Finite := by
    have hsub : Ky ⊆ Set.pi Set.univ (fun _ : Fin mh => Set.Iic Nbound) := by
      intro y hy i _
      exact hy i
    exact (Set.Finite.pi fun _ => Set.finite_Iic Nbound).subset hsub
  have hKyb_compact : IsCompact Kyb := by
    refine (isCompact_closedBall (0 : Fin mb → ℝ) B).inter_right ?_
    have : {yb : Fin mb → ℝ | 0 ≤ yb} = ⋂ i : Fin mb, {yb : Fin mb → ℝ | 0 ≤ yb i} := by
      ext yb; simp [Pi.le_def]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hK_compact : IsCompact (Ky ×ˢ Kyb) := hKy_fin.isCompact.prod hKyb_compact
  have hpn_mem : ∀ n, pn n ∈ Ky ×ˢ Kyb := by
    intro n
    refine ⟨?_, ?_, hpn_nn n⟩
    · intro i
      exact Nat.le_floor ((hpn_y n i).trans (hbound_n n))
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (hpn_yb n).trans (hbound_n n)
  obtain ⟨⟨y_lim, yb_lim⟩, ⟨_, _, hyb_lim_nn⟩, φ, hφ_mono, hφ_lim⟩ :=
    hK_compact.tendsto_subseq hpn_mem
  have hy_lim : Filter.Tendsto (fun n => (pn (φ n)).1) Filter.atTop (nhds y_lim) :=
    (continuous_fst.tendsto _).comp hφ_lim
  have hyb_lim : Filter.Tendsto (fun n => (pn (φ n)).2) Filter.atTop (nhds yb_lim) :=
    (continuous_snd.tendsto _).comp hφ_lim
  have htn_lim : Filter.Tendsto tn Filter.atTop (nhds t) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    refine (htndist n).trans ?_
    have hnR : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    have h1 : 1 / ε < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    have := (div_lt_iff₀ hε).mp h1
    linarith
  have htn_sub_lim : Filter.Tendsto (fun n => tn (φ n)) Filter.atTop (nhds t) :=
    htn_lim.comp hφ_mono.tendsto_atTop
  -- Continuity of constraint map and objective on (Fin mh → ℕ) × (Fin mb → ℝ)
  have hcast_lim : Filter.Tendsto (fun n => (fun i => ((pn (φ n)).1 i : ℝ)))
      Filter.atTop (nhds (fun i => (y_lim i : ℝ))) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    have hi : Filter.Tendsto (fun n => (pn (φ n)).1 i) Filter.atTop (nhds (y_lim i)) :=
      (continuous_apply i).tendsto _ |>.comp hy_lim
    exact (continuous_of_discreteTopology.tendsto _).comp hi
  have hmat_cont : ∀ {k : ℕ} (A : Matrix (Fin r) (Fin k) ℝ),
      Continuous (fun v : Fin k → ℝ => A *ᵥ v) := fun A => by
    refine continuous_pi fun i => ?_
    simp only [mulVec, dotProduct]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hlhs_lim : Filter.Tendsto
      (fun n => WithLp.toLp 2 (R.W *ᵥ (fun i => ((pn (φ n)).1 i : ℝ)) + R.Wb *ᵥ (pn (φ n)).2))
      Filter.atTop
      (nhds (WithLp.toLp 2 (R.W *ᵥ (fun i => (y_lim i : ℝ)) + R.Wb *ᵥ yb_lim))) := by
    have h1 := ((hmat_cont R.W).tendsto _).comp hcast_lim
    have h2 := ((hmat_cont R.Wb).tendsto _).comp hyb_lim
    exact ((WithLp.linearEquiv 2 ℝ (Fin r → ℝ)).symm.toLinearMap.toContinuousLinearMap.continuous.tendsto _).comp
      (h1.add h2)
  have hlhs_eq : (fun n => WithLp.toLp 2 (R.W *ᵥ (fun i => ((pn (φ n)).1 i : ℝ)) + R.Wb *ᵥ (pn (φ n)).2)) =
      (fun n => tn (φ n)) :=
    funext fun n => hpn_eq (φ n)
  rw [hlhs_eq] at hlhs_lim
  have heq_lim : WithLp.toLp 2 (R.W *ᵥ (fun i => (y_lim i : ℝ)) + R.Wb *ᵥ yb_lim) = t :=
    tendsto_nhds_unique hlhs_lim htn_sub_lim
  -- Pass cost inequality to the limit
  have hdot_cont : ∀ {k : ℕ} (c : Fin k → ℝ), Continuous (fun v : Fin k → ℝ => c ⬝ᵥ v) := fun c => by
    simp only [dotProduct]
    exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  have hcost_lim : Filter.Tendsto
      (fun n => R.q ⬝ᵥ (fun i => ((pn (φ n)).1 i : ℝ)) + R.qb ⬝ᵥ (pn (φ n)).2)
      Filter.atTop
      (nhds (R.q ⬝ᵥ (fun i => (y_lim i : ℝ)) + R.qb ⬝ᵥ yb_lim)) :=
    (((hdot_cont R.q).tendsto _).comp hcast_lim).add (((hdot_cont R.qb).tendsto _).comp hyb_lim)
  have hcost_le : R.q ⬝ᵥ (fun i => (y_lim i : ℝ)) + R.qb ⬝ᵥ yb_lim ≤ b :=
    le_of_tendsto hcost_lim (Filter.Eventually.of_forall fun n => le_of_lt (hpn_cost (φ n)))
  have hphi_le : R.Phi t ≤ (b : EReal) :=
    (phi_le_of_feasible R y_lim yb_lim hyb_lim_nn heq_lim).trans (EReal.coe_le_coe_iff.mpr hcost_le)
  exact not_lt_of_ge hphi_le hbt

private lemma phi_pseudo_lipschitz {r mh mb : ℕ} (R : Recourse r mh mb)
    (hB1 : R.B1) (hB3 : R.B3) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ t ∈ R.Tset, ∀ t' ∈ R.Tset,
      |(R.Phi t).toReal - (R.Phi t').toReal| ≤ α * ‖t - t'‖ + β := by
  have hfin := phi_ne_top_and_ne_bot R hB3
  let MQ := recourseRatMatrix R hB1
  let sgnQ (b : Bool) : ℚ := if b then 1 else -1
  let sgnR (b : Bool) : ℝ := if b then 1 else -1
  have hsgn_cast : ∀ b, (sgnQ b : ℝ) = sgnR b := fun b => by cases b <;> simp [sgnQ, sgnR]
  let MQ_σ (σ : (Fin mh ⊕ Fin mb) → Bool) : Matrix (Fin r) (Fin mh ⊕ Fin mb) ℚ :=
    fun i j => sgnQ (σ j) * MQ i j
  have hred_σ : ∀ σ : (Fin mh ⊕ Fin mb) → Bool,
      ∃ (C₀ C₁ : ℝ) (d : Finset (Fin mh ⊕ Fin mb) → (Fin mh ⊕ Fin mb) → ℕ),
        0 ≤ C₀ ∧ 0 ≤ C₁ ∧
        (∀ S, (MQ_σ σ).map (Rat.cast : ℚ → ℝ) *ᵥ (fun j => (d S j : ℝ)) = 0) ∧
        ∀ u : Fin mh ⊕ Fin mb → ℝ, 0 ≤ u →
          ∃ (u' : Fin mh ⊕ Fin mb → ℝ) (m : Finset (Fin mh ⊕ Fin mb) → ℕ),
            u = u' + ∑ S, (m S : ℝ) • (fun j => (d S j : ℝ)) ∧
            0 ≤ u' ∧
            (MQ_σ σ).map (Rat.cast : ℚ → ℝ) *ᵥ u' = (MQ_σ σ).map (Rat.cast : ℚ → ℝ) *ᵥ u ∧
            ‖u'‖ ≤ C₀ * ‖WithLp.toLp 2 ((MQ_σ σ).map (Rat.cast : ℚ → ℝ) *ᵥ u)‖ + C₁ :=
    fun σ => exists_bounded_reduction (MQ_σ σ)
  choose C₀_σ C₁_σ d_σ hC₀_σ hC₁_σ hd_σ hred using hred_σ
  let C₀_max : ℝ := ∑ σ : (Fin mh ⊕ Fin mb) → Bool, C₀_σ σ
  let C₁_max : ℝ := ∑ σ : (Fin mh ⊕ Fin mb) → Bool, C₁_σ σ
  have hC₀_max_nn : 0 ≤ C₀_max := Finset.sum_nonneg (fun σ _ => hC₀_σ σ)
  have hC₁_max_nn : 0 ≤ C₁_max := Finset.sum_nonneg (fun σ _ => hC₁_σ σ)
  let c : Fin mh ⊕ Fin mb → ℝ := Sum.elim R.q R.qb
  let Q_norm : ℝ := ∑ j : Fin mh ⊕ Fin mb, |c j|
  have hQ_nn : 0 ≤ Q_norm := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  let α : ℝ := Q_norm * C₀_max + 1
  let β : ℝ := Q_norm * C₁_max + 1
  have hα_pos : 0 < α := by positivity
  have hβ_pos : 0 < β := by positivity
  -- One-sided bound: (R.Phi t).toReal - (R.Phi t').toReal ≤ α * ‖t - t'‖ + β
  have hone_side : ∀ t ∈ R.Tset, ∀ t' ∈ R.Tset,
      (R.Phi t).toReal - (R.Phi t').toReal ≤ α * ‖t - t'‖ + β := by
    intro t ht t' ht'
    obtain ⟨hPhi_t_top, hPhi_t_bot⟩ := hfin t ht
    obtain ⟨hPhi_t'_top, hPhi_t'_bot⟩ := hfin t' ht'
    -- Pick a 1-optimal feasible solution (y', yb') for t'
    have hlt' : R.Phi t' < (((R.Phi t').toReal + 1 : ℝ) : EReal) :=
      calc R.Phi t' = ((R.Phi t').toReal : EReal) :=
            (EReal.coe_toReal hPhi_t'_top hPhi_t'_bot).symm
        _ < (((R.Phi t').toReal + 1 : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨y', yb', hyb'_nn, heq', hcost'⟩ := exists_feasible_lt_of_phi_lt R hlt'
    -- Pick any feasible solution (y, yb) for t
    obtain ⟨y, yb, hyb_nn, heq⟩ := ht
    let zt : Fin mh ⊕ Fin mb → ℝ := Sum.elim (fun i => (y i : ℝ)) yb
    let zt' : Fin mh ⊕ Fin mb → ℝ := Sum.elim (fun i => (y' i : ℝ)) yb'
    let Δ : Fin mh ⊕ Fin mb → ℝ := zt - zt'
    let σ : (Fin mh ⊕ Fin mb) → Bool := fun j => decide (0 ≤ Δ j)
    let u : Fin mh ⊕ Fin mb → ℝ := fun j => |Δ j|
    have hu_nn : 0 ≤ u := fun j => abs_nonneg _
    have hsgn_u : ∀ j, sgnR (σ j) * u j = Δ j := by
      intro j
      by_cases h : 0 ≤ Δ j
      · simp [σ, sgnR, u, h, abs_of_nonneg h]
      · have hlt : Δ j < 0 := not_le.mp h
        simp [σ, sgnR, u, h, abs_of_neg hlt]
    have hMσ_u : (MQ_σ σ).map (Rat.cast : ℚ → ℝ) *ᵥ u = (t - t').ofLp := by
      have hMt : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ zt = t.ofLp := by
        rw [block_mulVec_elim]; simpa using congr_arg WithLp.ofLp heq
      have hMt' : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ zt' = t'.ofLp := by
        rw [block_mulVec_elim]; simpa using congr_arg WithLp.ofLp heq'
      have hMΔ : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ Δ = (t - t').ofLp := by
        simp [Δ, Matrix.mulVec_sub, hMt, hMt']
      rw [← hMΔ]
      ext i
      simp only [mulVec, dotProduct, Matrix.map_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [MQ_σ, Rat.cast_mul, hsgn_cast]
      rw [mul_comm (sgnR (σ j)), mul_assoc, hsgn_u j]
    obtain ⟨u', m, hu_eq, hu'_nn, hMσ_u', hu'_norm⟩ := hred σ u hu_nn
    let Δ' : Fin mh ⊕ Fin mb → ℝ := fun j => sgnR (σ j) * u' j
    let z'' : Fin mh ⊕ Fin mb → ℝ := zt' + Δ'
    have hu'_le_u : ∀ j, u' j ≤ u j := by
      intro j
      have hj := congr_fun hu_eq j
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj
      have hsum_nn : 0 ≤ ∑ S, (m S : ℝ) * (d_σ σ S j : ℝ) :=
        Finset.sum_nonneg fun S _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith
    have hz''_nn : 0 ≤ z'' := by
      intro j
      simp only [z'', Δ', Pi.add_apply, Pi.zero_apply]
      by_cases h : 0 ≤ Δ j
      · have hzt'_nn : 0 ≤ zt' j := by
          cases j with
          | inl i => exact Nat.cast_nonneg _
          | inr i => exact hyb'_nn i
        have : sgnR (σ j) * u' j = u' j := by simp [σ, sgnR, h]
        rw [this]
        exact add_nonneg hzt'_nn (hu'_nn j)
      · have hlt : Δ j < 0 := not_le.mp h
        have hzt_nn : 0 ≤ zt j := by
          cases j with
          | inl i => exact Nat.cast_nonneg _
          | inr i => exact hyb_nn i
        have : sgnR (σ j) * u' j = -u' j := by simp [σ, sgnR, h]
        rw [this]
        have hu_val : u j = -Δ j := abs_of_neg hlt
        have hΔ_def : Δ j = zt j - zt' j := rfl
        linarith [hu'_le_u j]
    have hMz'' : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ z'' = t.ofLp := by
      have hMt' : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ zt' = t'.ofLp := by
        rw [block_mulVec_elim]; simpa using congr_arg WithLp.ofLp heq'
      have hMΔ' : MQ.map (Rat.cast : ℚ → ℝ) *ᵥ Δ' = (t - t').ofLp := by
        rw [← hMσ_u, ← hMσ_u']
        ext i
        simp only [mulVec, dotProduct, Matrix.map_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [MQ_σ, Δ', Rat.cast_mul, hsgn_cast]
        ring
      rw [show z'' = zt' + Δ' from rfl, Matrix.mulVec_add, hMt', hMΔ']
      simp
    -- Extract integer coordinates for the first mh entries of z''
    have hy''_nat : ∀ i : Fin mh, ∃ k : ℕ, z'' (Sum.inl i) = (k : ℝ) := by
      intro i
      let j : Fin mh ⊕ Fin mb := Sum.inl i
      have hΔ_int : Δ j = ((y i : ℤ) - (y' i : ℤ) : ℝ) := by
        simp [Δ, zt, zt', j]
      let diffZ : ℤ := (y i : ℤ) - (y' i : ℤ)
      have hu_nat : u j = (diffZ.natAbs : ℝ) := by
        have h1 : Δ j = (diffZ : ℝ) := by simp [diffZ, hΔ_int]
        have h2 : |(diffZ : ℝ)| = ((|diffZ| : ℤ) : ℝ) := (Int.cast_abs (a := diffZ)).symm
        have h3 : (|diffZ| : ℤ) = (diffZ.natAbs : ℤ) := Int.abs_eq_natAbs diffZ
        simp only [u, h1, h2, h3, Int.cast_natCast]
      let sub : ℕ := ∑ S, m S * d_σ σ S j
      have hsubR : (sub : ℝ) = ∑ S, (m S : ℝ) * (d_σ σ S j : ℝ) := by simp [sub]
      have hj_eq := congr_fun hu_eq j
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj_eq
      have hle : sub ≤ diffZ.natAbs := by
        have hR : (sub : ℝ) ≤ (diffZ.natAbs : ℝ) := by
          have h0 : 0 ≤ u' j := hu'_nn j
          linarith [hu_nat, hsubR, hj_eq]
        exact Nat.cast_le.mp hR
      let k0 : ℕ := diffZ.natAbs - sub
      have hu'_k0 : u' j = (k0 : ℝ) := by
        rw [Nat.cast_sub hle, hsubR]
        linarith [hu_nat, hj_eq]
      let sZ : ℤ := if σ j then 1 else -1
      have hsZ_eq : (sZ : ℝ) = sgnR (σ j) := by cases hσ : σ j <;> simp [sZ, sgnR, hσ]
      let valZ : ℤ := (y' i : ℤ) + sZ * (k0 : ℤ)
      have hvalZ_eq : (valZ : ℝ) = z'' j := by
        simp only [valZ, z'', Δ', zt', j, Sum.elim_inl, Pi.add_apply, Int.cast_add,
          Int.cast_mul, Int.cast_natCast, hsZ_eq, hu'_k0]
      have hvalZ_nn : 0 ≤ valZ := by
        have hR : (0 : ℝ) ≤ (valZ : ℝ) := by rw [hvalZ_eq]; exact hz''_nn j
        exact_mod_cast hR
      refine ⟨valZ.toNat, ?_⟩
      have htoNat : ((valZ.toNat : ℕ) : ℤ) = valZ := Int.toNat_of_nonneg hvalZ_nn
      have hR : (valZ.toNat : ℝ) = (valZ : ℝ) := by exact_mod_cast htoNat
      exact hvalZ_eq.symm.trans hR.symm
    choose y'' hy''_eq using hy''_nat
    let yb'' : Fin mb → ℝ := fun i => z'' (Sum.inr i)
    have hz''_elim : z'' = Sum.elim (fun i => (y'' i : ℝ)) yb'' := by
      ext j; cases j with
      | inl i => exact hy''_eq i
      | inr i => rfl
    have hyb''_nn : 0 ≤ yb'' := fun i => hz''_nn (Sum.inr i)
    have heq'' : WithLp.toLp 2 (R.W *ᵥ (fun i => (y'' i : ℝ)) + R.Wb *ᵥ yb'') = t := by
      apply WithLp.ofLp_injective 2
      rw [← block_mulVec_elim R hB1, ← hz''_elim]
      exact hMz''
    have hphi_le : (R.Phi t).toReal ≤ R.q ⬝ᵥ (fun i => (y'' i : ℝ)) + R.qb ⬝ᵥ yb'' := by
      have hle := phi_le_of_feasible R y'' yb'' hyb''_nn heq''
      rw [← EReal.coe_toReal hPhi_t_top hPhi_t_bot] at hle
      exact EReal.coe_le_coe_iff.mp hle
    have hcost_decomp : R.q ⬝ᵥ (fun i => (y'' i : ℝ)) + R.qb ⬝ᵥ yb'' =
        (R.q ⬝ᵥ (fun i => (y' i : ℝ)) + R.qb ⬝ᵥ yb') + c ⬝ᵥ Δ' := by
      have h1 : c ⬝ᵥ z'' = R.q ⬝ᵥ (fun i => (y'' i : ℝ)) + R.qb ⬝ᵥ yb'' := by
        rw [hz''_elim]; simp [c, dotProduct, Fintype.sum_sum_type]
      have h2 : c ⬝ᵥ zt' = R.q ⬝ᵥ (fun i => (y' i : ℝ)) + R.qb ⬝ᵥ yb' := by
        simp [c, zt', dotProduct, Fintype.sum_sum_type]
      rw [← h1, ← h2, show z'' = zt' + Δ' from rfl, dotProduct_add]
    have hnorm_Δ' : ‖Δ'‖ = ‖u'‖ := by
      apply le_antisymm
      · rw [pi_norm_le_iff_of_nonneg (norm_nonneg u')]
        intro j
        have habs : |sgnR (σ j)| = 1 := by cases σ j <;> simp [sgnR]
        calc ‖Δ' j‖ = |sgnR (σ j) * u' j| := rfl
          _ = |sgnR (σ j)| * |u' j| := abs_mul _ _
          _ = ‖u' j‖ := by rw [habs, one_mul]; rfl
          _ ≤ ‖u'‖ := norm_le_pi_norm u' j
      · rw [pi_norm_le_iff_of_nonneg (norm_nonneg Δ')]
        intro j
        have habs : |sgnR (σ j)| = 1 := by cases σ j <;> simp [sgnR]
        calc ‖u' j‖ = |sgnR (σ j)| * |u' j| := by rw [habs, one_mul]; rfl
          _ = |sgnR (σ j) * u' j| := (abs_mul _ _).symm
          _ = ‖Δ' j‖ := rfl
          _ ≤ ‖Δ'‖ := norm_le_pi_norm Δ' j
    have hcΔ' : c ⬝ᵥ Δ' ≤ Q_norm * ‖u'‖ := by
      rw [← hnorm_Δ']
      calc c ⬝ᵥ Δ'
          ≤ ∑ j : Fin mh ⊕ Fin mb, |c j * Δ' j| :=
            Finset.sum_le_sum fun j _ => le_abs_self _
        _ = ∑ j : Fin mh ⊕ Fin mb, |c j| * ‖Δ' j‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [abs_mul]; rfl
        _ ≤ ∑ j : Fin mh ⊕ Fin mb, |c j| * ‖Δ'‖ :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (norm_le_pi_norm Δ' j) (abs_nonneg _)
        _ = Q_norm * ‖Δ'‖ := (Finset.sum_mul _ _ _).symm
    have hC₀_le : C₀_σ σ ≤ C₀_max :=
      Finset.single_le_sum (fun τ _ => hC₀_σ τ) (Finset.mem_univ σ)
    have hC₁_le : C₁_σ σ ≤ C₁_max :=
      Finset.single_le_sum (fun τ _ => hC₁_σ τ) (Finset.mem_univ σ)
    have hu'_bound : ‖u'‖ ≤ C₀_max * ‖t - t'‖ + C₁_max := by
      rw [hMσ_u] at hu'_norm
      have h1 : C₀_σ σ * ‖t - t'‖ ≤ C₀_max * ‖t - t'‖ :=
        mul_le_mul_of_nonneg_right hC₀_le (norm_nonneg _)
      linarith
    have hQ_bound : Q_norm * ‖u'‖ ≤ Q_norm * (C₀_max * ‖t - t'‖ + C₁_max) :=
      mul_le_mul_of_nonneg_left hu'_bound hQ_nn
    have hnorm_nn : 0 ≤ ‖t - t'‖ := norm_nonneg _
    have hα_step : Q_norm * C₀_max * ‖t - t'‖ ≤ α * ‖t - t'‖ := by
      dsimp only [α]
      nlinarith
    linarith
  refine ⟨α, β, hα_pos, hβ_pos, fun t ht t' ht' => ?_⟩
  rw [abs_sub_le_iff]
  refine ⟨hone_side t ht t' ht', ?_⟩
  simpa [norm_sub_rev] using hone_side t' ht' t ht

end Helpers

theorem solution {r mh mb : ℕ} (R : ProbMetricStab.MixedInt.Recourse r mh mb)
    (hB1 : R.B1) (hB3 : R.B3) :
    (∀ t ∈ R.Tset, R.Phi t ≠ ⊤ ∧ R.Phi t ≠ ⊥) ∧
    LowerSemicontinuousOn R.Phi R.Tset ∧
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ t ∈ R.Tset, ∀ t' ∈ R.Tset,
      |(R.Phi t).toReal - (R.Phi t').toReal| ≤ α * ‖t - t'‖ + β :=
  ⟨phi_ne_top_and_ne_bot R hB3,
   phi_lowerSemicontinuousOn R hB1 hB3,
   phi_pseudo_lipschitz R hB1 hB3⟩
