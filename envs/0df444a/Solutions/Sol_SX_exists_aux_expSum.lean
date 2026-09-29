-- Prove2me | solution 1 for SX.exists_aux_expSum
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T14:56:25.07371+00:00
-- url     : https://prove2.me/submissions/b09434ad-f78b-47d4-8eb8-16f7843e66e4

import Definitions.Def_SX

open Complex

namespace AuxSiegel

open NumberField Matrix Finset Module

attribute [local instance] Matrix.seminormedAddCommGroup

section Fixed

variable (K : Type*) [Field K] [NumberField K] [DecidableEq (K →+* ℂ)]

noncomputable def cc : ℝ := (finrank ℚ K : ℝ) * ‖((basisMatrix K).transpose)⁻¹‖

noncomputable def bas : Basis (K →+* ℂ) ℤ (𝓞 K) :=
  (RingOfIntegers.basis K).reindex (equivReindex K).symm

variable {K}

set_option backward.isDefEq.respectTransparency false in
lemma repr_abs_le (α : 𝓞 K) (r : K →+* ℂ) :
    |((bas K).repr α r : ℝ)| ≤ cc K * house (algebraMap (𝓞 K) K α) := by
  have h := NumberField.house.basis_repr_norm_le_const_mul_house K α r
  simp only [Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
    NumberField.integralBasis_repr_apply, eq_intCast, Rat.cast_intCast,
    Complex.norm_intCast] at h
  rw [bas]
  simp only [Basis.repr_reindex, Finsupp.mapDomain_equiv_apply]
  exact_mod_cast h


/-- Siegel's lemma for a system with algebraic-integer coefficients and *rational integer*
unknowns: the `ℤ`-coordinates of the coefficients w.r.t. an integral basis form an integer
matrix with `card ρ * [K:ℚ]` rows and `card κ` columns. -/
theorem exists_int_kernel {K : Type*} [Field K] [NumberField K] [DecidableEq (K →+* ℂ)]
    {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    (a : ρ → κ → 𝓞 K) {A : ℝ}
    (hA : ∀ k lam, house (algebraMap (𝓞 K) K (a k lam)) ≤ A)
    (hlt : Fintype.card ρ * finrank ℚ K < Fintype.card κ)
    (hpos : 0 < Fintype.card ρ)
    (hhalf : 2 * (Fintype.card ρ * finrank ℚ K) ≤ Fintype.card κ) :
    ∃ t : κ → ℤ, t ≠ 0 ∧ (∀ k, ∑ lam, t lam • a k lam = 0) ∧
      ∀ lam, |(t lam : ℝ)| ≤ Fintype.card κ * max 1 (cc K * A) := by
  classical
  have hccnn : (0:ℝ) ≤ cc K := by
    rw [cc]; positivity
  have hAnn : 0 ≤ A := by
    obtain ⟨k⟩ := Fintype.card_pos_iff.1 hpos
    obtain ⟨lam⟩ := Fintype.card_pos_iff.1 (lt_of_le_of_lt (Nat.zero_le _) hlt)
    exact le_trans (house_nonneg _) (hA k lam)
  set C : Matrix (ρ × (K →+* ℂ)) κ ℤ := fun kr lam => (bas K).repr (a kr.1 lam) kr.2 with hC
  have hrow : Fintype.card (ρ × (K →+* ℂ)) = Fintype.card ρ * finrank ℚ K := by
    rw [Fintype.card_prod, Embeddings.card]
  have hm : 0 < Fintype.card (ρ × (K →+* ℂ)) := by
    rw [hrow]; exact Nat.mul_pos hpos finrank_pos
  have hn : Fintype.card (ρ × (K →+* ℂ)) < Fintype.card κ := by rw [hrow]; exact hlt
  obtain ⟨t, ht0, hker, hbd⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le C hn hm
  refine ⟨t, ht0, ?_, ?_⟩
  · intro k
    have : (bas K).repr (∑ lam, t lam • a k lam) = 0 := by
      ext r
      have := congrFun hker (k, r)
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, hC] at this
      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun lam _ => mul_comm _ _
    simpa using (bas K).repr.map_eq_zero_iff.mp this
  · intro lam
    have hnormC : ‖C‖ ≤ cc K * A := by
      rw [Matrix.norm_le_iff (by positivity)]
      intro kr l
      rw [Int.norm_eq_abs, ← Int.cast_abs]
      calc ((|C kr l| : ℤ) : ℝ) = |((C kr l : ℤ) : ℝ)| := by push_cast; ring
        _ ≤ cc K * house (algebraMap (𝓞 K) K (a kr.1 l)) := repr_abs_le _ _
        _ ≤ cc K * A := by
            exact mul_le_mul_of_nonneg_left (hA _ _) hccnn
    have hmax : max 1 ‖C‖ ≤ max 1 (cc K * A) := max_le_max le_rfl hnormC
    have hcardk : 1 ≤ (Fintype.card κ : ℝ) := by
      have : 0 < Fintype.card κ := lt_of_le_of_lt (Nat.zero_le _) hn
      exact_mod_cast this
    have hbase1 : (1:ℝ) ≤ (Fintype.card κ : ℝ) * max 1 ‖C‖ := by
      have h1 : (1:ℝ) ≤ max 1 ‖C‖ := le_max_left _ _
      nlinarith
    have hexp : ((Fintype.card (ρ × (K →+* ℂ)) : ℝ) /
        ((Fintype.card κ : ℝ) - Fintype.card (ρ × (K →+* ℂ)))) ≤ 1 := by
      have h2 : 2 * (Fintype.card (ρ × (K →+* ℂ)) : ℝ) ≤ (Fintype.card κ : ℝ) := by
        rw [hrow]; exact_mod_cast hhalf
      have h3 : (0:ℝ) < (Fintype.card κ : ℝ) - Fintype.card (ρ × (K →+* ℂ)) := by
        have : (Fintype.card (ρ × (K →+* ℂ)) : ℝ) < Fintype.card κ := by exact_mod_cast hn
        linarith
      rw [div_le_one h3]
      linarith
    calc |(t lam : ℝ)| ≤ ‖t‖ := by
          have h := norm_le_pi_norm t lam
          rw [Int.norm_eq_abs] at h
          push_cast at h
          exact h
      _ ≤ ((Fintype.card κ : ℝ) * max 1 ‖C‖) ^
            ((Fintype.card (ρ × (K →+* ℂ)) : ℝ) /
              ((Fintype.card κ : ℝ) - Fintype.card (ρ × (K →+* ℂ)))) := hbd
      _ ≤ ((Fintype.card κ : ℝ) * max 1 ‖C‖) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase1 hexp
      _ = (Fintype.card κ : ℝ) * max 1 ‖C‖ := Real.rpow_one _
      _ ≤ (Fintype.card κ : ℝ) * max 1 (cc K * A) := by
            exact mul_le_mul_of_nonneg_left hmax (by linarith)

end Fixed

end AuxSiegel

namespace AuxSiegel

open NumberField Finset

/-- Indexed submultiplicativity of the house over a product. -/
lemma house_prod_le' {K : Type*} [Field K] [NumberField K] {ι : Type*}
    (s : Finset ι) (f : ι → K) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  simpa only [house, map_prod] using
    Finset.norm_prod_le s (fun i => canonicalEmbedding K (f i))

lemma prod_prod_mul_pow {K : Type*} [CommRing K] {d l : ℕ} (bK : K)
    (θ : Fin d → Fin l → K) (e : Fin d → Fin l → ℕ) :
    ∏ i, ∏ j, (bK * θ i j) ^ e i j
      = bK ^ (∑ i, ∑ j, e i j) * ∏ i, ∏ j, θ i j ^ e i j := by
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end AuxSiegel

open NumberField Finset AuxSiegel in
open SX in
theorem solution
    {d l : ℕ} (hdl : d + l < d * l)
    (x : Fin d → ℂ) (y : Fin l → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y)
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ i j, Complex.exp (x i * y j) ∈ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ∃ L : ℕ, 0 < L ∧ (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l ∧
        ∃ p : (Fin d → ℕ) → ℤ,
          (∃ lam ∈ SX.box d L, p lam ≠ 0) ∧
          (∀ lam, |(p lam : ℝ)| ≤ Real.exp (c * L * M)) ∧
          (∀ m : Fin l → ℕ, (∀ j, m j < M) → SX.expSum x L p (SX.latticeSum y m) = 0) := by
  classical
  haveI : NumberField K := ⟨⟩
  have hd2 : 2 ≤ d := by by_contra h; push_neg at h; interval_cases d <;> omega
  have hl2 : 2 ≤ l := by by_contra h; push_neg at h; interval_cases l <;> omega
  set n : ℕ := Module.finrank ℚ K with hndef
  have hn1 : 1 ≤ n := Module.finrank_pos
  -- the inclusion `K → ℂ` as a ring hom
  set V : K →+* ℂ := (IntermediateField.val K).toRingHom with hVdef
  have hVinj : Function.Injective V := V.injective
  -- the six numbers, as elements of `K`
  set θ : Fin d → Fin l → K := fun i j => ⟨Complex.exp (x i * y j), hK i j⟩ with hθdef
  have hVθ : ∀ i j, V (θ i j) = Complex.exp (x i * y j) := fun i j => rfl
  -- a common denominator
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors (𝓞 K)) (fun ij : Fin d × Fin l => θ ij.1 ij.2)
  set bK : K := algebraMap (𝓞 K) K (b : 𝓞 K) with hbKdef
  have hbK0 : bK ≠ 0 := by
    have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
    simpa [hbKdef, map_eq_zero_iff _ hinj] using nonZeroDivisors.coe_ne_zero b
  have hb' : ∀ ij : Fin d × Fin l, ∃ v : 𝓞 K,
      algebraMap (𝓞 K) K v = bK * θ ij.1 ij.2 := by
    intro ij
    obtain ⟨v, hv⟩ := hb ij
    exact ⟨v, by rw [hv, Algebra.smul_def]⟩
  choose u hu using hb'
  -- the uniform house bound `H`
  set H : ℝ := 1 + house bK + ∑ i : Fin d, ∑ j : Fin l, house (bK * θ i j) with hHdef
  have hsum_nonneg : (0:ℝ) ≤ ∑ i : Fin d, ∑ j : Fin l, house (bK * θ i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => house_nonneg _
  have hH1 : (1:ℝ) ≤ H := by
    have := house_nonneg bK; rw [hHdef]; linarith
  have hHb : house bK ≤ H := by
    have := house_nonneg bK; rw [hHdef]; linarith
  have hHQ : ∀ i j, house (bK * θ i j) ≤ H := by
    intro i j
    have h1 : house (bK * θ i j) ≤ ∑ j' : Fin l, house (bK * θ i j') :=
      Finset.single_le_sum (f := fun j' => house (bK * θ i j'))
        (fun j' _ => house_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ j' : Fin l, house (bK * θ i j'))
        ≤ ∑ i' : Fin d, ∑ j' : Fin l, house (bK * θ i' j') :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin l, house (bK * θ i' j'))
        (fun i' _ => Finset.sum_nonneg fun j' _ => house_nonneg _) (Finset.mem_univ i)
    have := house_nonneg bK
    rw [hHdef]; linarith
  have hlogH : (0:ℝ) ≤ Real.log H := Real.log_nonneg hH1
  set W : ℝ := max 1 (AuxSiegel.cc K) with hWdef
  have hW1 : (1:ℝ) ≤ W := le_max_left _ _
  have hlogW : (0:ℝ) ≤ Real.log W := Real.log_nonneg hW1
  set c : ℝ := ((2 ^ d * 2 * n : ℕ) : ℝ) + (d : ℝ) + Real.log W
      + ((d * l : ℕ) : ℝ) * Real.log H + 1 with hcdef
  have hc0 : 0 < c := by
    have h1 : (0:ℝ) ≤ ((2 ^ d * 2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ ((d * l : ℕ) : ℝ) * Real.log H :=
      mul_nonneg (Nat.cast_nonneg _) hlogH
    rw [hcdef]; linarith
  refine ⟨c, hc0, 1, ?_⟩
  intro M hM1
  have hM0 : 0 < M := hM1
  -- choose `L`
  have hex : ∃ LL : ℕ, 2 * n * M ^ l ≤ LL ^ d := ⟨2 * n * M ^ l, Nat.le_self_pow (by omega) _⟩
  set L : ℕ := Nat.find hex with hLdef
  have hLspec : 2 * n * M ^ l ≤ L ^ d := Nat.find_spec hex
  have hMl1 : 1 ≤ M ^ l := Nat.one_le_pow _ _ hM0
  have hSpos : 1 ≤ 2 * n * M ^ l := by nlinarith
  have hL0 : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h, Nat.zero_pow (show 0 < d by omega)] at hLspec; omega
    · exact h
  have hLub : L ^ d ≤ 2 ^ d * (2 * n * M ^ l) := by
    rcases Nat.lt_or_ge L 2 with h | h
    · have hL1 : L = 1 := by omega
      have : (1:ℕ) ≤ 2 ^ d := Nat.one_le_two_pow
      calc L ^ d = 1 := by rw [hL1]; simp
        _ ≤ 2 * n * M ^ l := hSpos
        _ ≤ 2 ^ d * (2 * n * M ^ l) := Nat.le_mul_of_pos_left _ (by omega)
    · have hmin := Nat.find_min hex (m := L - 1) (by omega)
      push_neg at hmin
      have hstep : L ≤ 2 * (L - 1) := by omega
      calc L ^ d ≤ (2 * (L - 1)) ^ d := Nat.pow_le_pow_left hstep d
        _ = 2 ^ d * (L - 1) ^ d := by rw [mul_pow]
        _ ≤ 2 ^ d * (2 * n * M ^ l) := Nat.mul_le_mul_left _ (le_of_lt hmin)
  have hLc : (L : ℝ) ^ d ≤ c * (M : ℝ) ^ l := by
    have h1 : ((L ^ d : ℕ) : ℝ) ≤ ((2 ^ d * 2 * n * M ^ l : ℕ) : ℝ) := by
      exact_mod_cast (by rw [mul_assoc (2^d * 2) n (M^l)] at *; linarith [hLub, (by ring_nf : (2:ℕ)^d * (2*n*M^l) = 2^d*2*n*M^l)] : L ^ d ≤ 2 ^ d * 2 * n * M ^ l)
    push_cast at h1
    have h2 : (0:ℝ) ≤ (M:ℝ) ^ l := by positivity
    have h3 : ((2 ^ d * 2 * n : ℕ) : ℝ) ≤ c := by
      have := mul_nonneg (Nat.cast_nonneg (d*l) : (0:ℝ) ≤ ((d*l : ℕ):ℝ)) hlogH
      have h2' : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
      rw [hcdef]; linarith
    calc (L:ℝ) ^ d ≤ ((2 ^ d * 2 * n : ℕ) : ℝ) * (M:ℝ) ^ l := by push_cast at h1 ⊢; linarith
      _ ≤ c * (M:ℝ) ^ l := by exact mul_le_mul_of_nonneg_right h3 h2
  
  -- the coefficient matrix over the ring of integers
  set T : ℕ := d * l * L * M with hTdef
  set aM : (Fin l → Fin M) → {lam : Fin d → ℕ // lam ∈ SX.box d L} → 𝓞 K :=
    fun m lam => (b : 𝓞 K) ^ (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ)) *
      ∏ i, ∏ j, u (i, j) ^ (lam.1 i * (m j : ℕ)) with haMdef
  have hEle : ∀ (m : Fin l → Fin M) (lam : {lam : Fin d → ℕ // lam ∈ SX.box d L}),
      (∑ i, ∑ j, lam.1 i * (m j : ℕ)) ≤ T := by
    intro m lam
    have h1 : ∀ (i : Fin d) (j : Fin l), lam.1 i * (m j : ℕ) ≤ L * M := by
      intro i j
      exact Nat.mul_le_mul (le_of_lt (SX.mem_box.mp lam.2 i)) (le_of_lt (m j).2)
    have h2 : (∑ i : Fin d, ∑ j : Fin l, lam.1 i * (m j : ℕ))
        ≤ ∑ _i : Fin d, ∑ _j : Fin l, (L * M) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    have h3 : (∑ _i : Fin d, ∑ _j : Fin l, (L * M)) = T := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hTdef]
      ring
    omega
  have hmap1 : ∀ (m : Fin l → Fin M) (lam : {lam : Fin d → ℕ // lam ∈ SX.box d L}),
      algebraMap (𝓞 K) K (aM m lam)
        = bK ^ (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ))
          * ∏ i, ∏ j, (bK * θ i j) ^ (lam.1 i * (m j : ℕ)) := by
    intro m lam
    rw [haMdef]
    simp only [map_mul, map_pow, map_prod, hu, ← hbKdef]
  have hmap2 : ∀ (m : Fin l → Fin M) (lam : {lam : Fin d → ℕ // lam ∈ SX.box d L}),
      algebraMap (𝓞 K) K (aM m lam)
        = bK ^ T * ∏ i, ∏ j, θ i j ^ (lam.1 i * (m j : ℕ)) := by
    intro m lam
    have hTE : (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ)) + (∑ i, ∑ j, lam.1 i * (m j : ℕ)) = T := by
      have := hEle m lam; omega
    rw [hmap1, AuxSiegel.prod_prod_mul_pow, ← mul_assoc, ← pow_add, hTE]
  have hH0 : (0:ℝ) < H := by linarith
  have hAbound : ∀ (m : Fin l → Fin M) (lam : {lam : Fin d → ℕ // lam ∈ SX.box d L}),
      house (algebraMap (𝓞 K) K (aM m lam)) ≤ H ^ T := by
    intro m lam
    have hE := hEle m lam
    have s1 : house (bK ^ (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ)))
        ≤ H ^ (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ)) :=
      le_trans (house_pow_le _ _) (pow_le_pow_left₀ (house_nonneg _) hHb _)
    have s2 : house (∏ i, ∏ j, (bK * θ i j) ^ (lam.1 i * (m j : ℕ)))
        ≤ ∏ i : Fin d, ∏ j : Fin l, H ^ (lam.1 i * (m j : ℕ)) := by
      refine le_trans (AuxSiegel.house_prod_le' _ _) ?_
      refine Finset.prod_le_prod (fun i _ => house_nonneg _) (fun i _ => ?_)
      refine le_trans (AuxSiegel.house_prod_le' _ _) ?_
      refine Finset.prod_le_prod (fun j _ => house_nonneg _) (fun j _ => ?_)
      exact le_trans (house_pow_le _ _) (pow_le_pow_left₀ (house_nonneg _) (hHQ i j) _)
    have s3 : (∏ i : Fin d, ∏ j : Fin l, H ^ (lam.1 i * (m j : ℕ)))
        = H ^ (∑ i, ∑ j, lam.1 i * (m j : ℕ)) := by
      simp only [Finset.prod_pow_eq_pow_sum]
    rw [hmap1]
    calc house (bK ^ (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ))
            * ∏ i, ∏ j, (bK * θ i j) ^ (lam.1 i * (m j : ℕ)))
        ≤ house (bK ^ (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ)))
            * house (∏ i, ∏ j, (bK * θ i j) ^ (lam.1 i * (m j : ℕ))) := house_mul_le _ _
      _ ≤ H ^ (T - ∑ i, ∑ j, lam.1 i * (m j : ℕ)) * H ^ (∑ i, ∑ j, lam.1 i * (m j : ℕ)) := by
          rw [← s3]
          exact mul_le_mul s1 s2 (house_nonneg _) (pow_nonneg (le_of_lt hH0) _)
      _ = H ^ T := by
          rw [← pow_add]
          congr 1
          omega
  -- cardinalities
  have hcardr : Fintype.card (Fin l → Fin M) = M ^ l := by simp
  have hcardk : Fintype.card {lam : Fin d → ℕ // lam ∈ SX.box d L} = L ^ d := by
    rw [Fintype.card_coe]
    simp [SX.box]
  have hone : 1 ≤ M ^ l * n := by
    calc 1 = 1 * 1 := by ring
      _ ≤ M ^ l * n := Nat.mul_le_mul hMl1 hn1
  have hpos : 0 < Fintype.card (Fin l → Fin M) := by rw [hcardr]; omega
  have hhalf : 2 * (Fintype.card (Fin l → Fin M) * Module.finrank ℚ K)
      ≤ Fintype.card {lam : Fin d → ℕ // lam ∈ SX.box d L} := by
    rw [hcardr, hcardk, ← hndef]
    calc 2 * (M ^ l * n) = 2 * n * M ^ l := by ring
      _ ≤ L ^ d := hLspec
  have hlt : Fintype.card (Fin l → Fin M) * Module.finrank ℚ K
      < Fintype.card {lam : Fin d → ℕ // lam ∈ SX.box d L} := by
    have h := hhalf
    rw [hcardr, hcardk, ← hndef] at h ⊢
    omega
  obtain ⟨t, ht0, hker, hbd⟩ :=
    AuxSiegel.exists_int_kernel (K := K) aM hAbound hlt hpos hhalf
  -- the height estimate
  have hHT1 : (1:ℝ) ≤ H ^ T := one_le_pow₀ hH1
  have hL1R : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL0
  have hM1R : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM0
  have hHTexp : H ^ T = Real.exp (((d * l : ℕ) : ℝ) * Real.log H * (L:ℝ) * (M:ℝ)) := by
    conv_lhs => rw [← Real.exp_log hH0]
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hTdef]
    push_cast
    ring
  have hWexp : W ≤ Real.exp (Real.log W * (L:ℝ) * (M:ℝ)) := by
    have hW0 : (0:ℝ) < W := by linarith
    conv_lhs => rw [← Real.exp_log hW0]
    refine Real.exp_le_exp.mpr ?_
    have hA : Real.log W ≤ Real.log W * (L:ℝ) := le_mul_of_one_le_right hlogW hL1R
    have hB : Real.log W * (L:ℝ) ≤ Real.log W * (L:ℝ) * (M:ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hlogW (by linarith)) hM1R
    linarith
  have hLdexp : (L:ℝ) ^ d ≤ Real.exp ((d:ℝ) * (L:ℝ) * (M:ℝ)) := by
    have h1 : (L:ℝ) ≤ Real.exp (L:ℝ) := by linarith [Real.add_one_le_exp (L:ℝ)]
    have hdR : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg _
    calc (L:ℝ) ^ d ≤ (Real.exp (L:ℝ)) ^ d :=
          pow_le_pow_left₀ (by linarith) h1 d
      _ = Real.exp ((d:ℝ) * (L:ℝ)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((d:ℝ) * (L:ℝ) * (M:ℝ)) := Real.exp_le_exp.mpr
            (le_mul_of_one_le_right (mul_nonneg hdR (by linarith)) hM1R)
  have hcoef : (d:ℝ) + Real.log W + ((d * l : ℕ) : ℝ) * Real.log H ≤ c := by
    have h0 : (0:ℝ) ≤ ((2 ^ d * 2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hcdef]; linarith
  have hheight : ∀ lam : {lam : Fin d → ℕ // lam ∈ SX.box d L},
      |((t lam : ℤ) : ℝ)| ≤ Real.exp (c * (L:ℝ) * (M:ℝ)) := by
    intro lam
    refine le_trans (hbd lam) ?_
    have hmax : max 1 (AuxSiegel.cc K * H ^ T) ≤ W * H ^ T := by
      refine max_le ?_ ?_
      · nlinarith
      · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hcardR : ((Fintype.card {lam : Fin d → ℕ // lam ∈ SX.box d L} : ℕ) : ℝ) = (L:ℝ) ^ d := by
      rw [hcardk]; push_cast; ring
    calc ((Fintype.card {lam : Fin d → ℕ // lam ∈ SX.box d L} : ℕ) : ℝ)
            * max 1 (AuxSiegel.cc K * H ^ T)
        ≤ (L:ℝ) ^ d * (W * H ^ T) := by
          rw [hcardR]
          exact mul_le_mul_of_nonneg_left hmax (by positivity)
      _ ≤ Real.exp ((d:ℝ) * (L:ℝ) * (M:ℝ))
            * (Real.exp (Real.log W * (L:ℝ) * (M:ℝ))
              * Real.exp (((d * l : ℕ) : ℝ) * Real.log H * (L:ℝ) * (M:ℝ))) := by
          rw [hHTexp] at hmax ⊢
          refine mul_le_mul hLdexp ?_ (by positivity) (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_right hWexp (Real.exp_nonneg _)
      _ = Real.exp (((d:ℝ) + Real.log W + ((d * l : ℕ) : ℝ) * Real.log H) * (L:ℝ) * (M:ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (c * (L:ℝ) * (M:ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have hLM0 : (0:ℝ) ≤ (L:ℝ) * (M:ℝ) := by positivity
          calc ((d:ℝ) + Real.log W + ((d * l : ℕ) : ℝ) * Real.log H) * (L:ℝ) * (M:ℝ)
              = ((d:ℝ) + Real.log W + ((d * l : ℕ) : ℝ) * Real.log H) * ((L:ℝ) * (M:ℝ)) := by ring
            _ ≤ c * ((L:ℝ) * (M:ℝ)) := mul_le_mul_of_nonneg_right hcoef hLM0
            _ = c * (L:ℝ) * (M:ℝ) := by ring
  -- assemble
  set pp : (Fin d → ℕ) → ℤ :=
    fun lam => if h : lam ∈ SX.box d L then t ⟨lam, h⟩ else 0 with hppdef
  have hp : ∀ lam : {lam : Fin d → ℕ // lam ∈ SX.box d L}, pp lam.1 = t lam :=
    fun lam => dif_pos lam.2
  have hp0 : ∀ lam, lam ∉ SX.box d L → pp lam = 0 := fun lam h => dif_neg h
  refine ⟨L, hL0, hLc, pp, ?_, ?_, ?_⟩
  · obtain ⟨lam, hlam⟩ := Function.ne_iff.mp ht0
    refine ⟨lam.1, lam.2, ?_⟩
    rw [hp lam]
    simpa using hlam
  · intro lam
    by_cases h : lam ∈ SX.box d L
    · have := hheight ⟨lam, h⟩
      rwa [← hp ⟨lam, h⟩] at this
    · rw [hp0 lam h]
      simpa using (Real.exp_pos (c * (L:ℝ) * (M:ℝ))).le
  · intro m hm
    have hker' := hker (fun j => (⟨m j, hm j⟩ : Fin M))
    have hVsum : ∑ lam : {lam : Fin d → ℕ // lam ∈ SX.box d L},
        ((t lam : ℤ) : ℂ) * V (algebraMap (𝓞 K) K (aM (fun j => (⟨m j, hm j⟩ : Fin M)) lam)) = 0 := by
      have h := congrArg (fun z : 𝓞 K => V (algebraMap (𝓞 K) K z)) hker'
      simpa [map_sum, map_zsmul, zsmul_eq_mul] using h
    have hVa : ∀ lam : {lam : Fin d → ℕ // lam ∈ SX.box d L},
        V (algebraMap (𝓞 K) K (aM (fun j => (⟨m j, hm j⟩ : Fin M)) lam))
          = (V bK) ^ T * Complex.exp (SX.expExponent x lam.1 * SX.latticeSum y m) := by
      intro lam
      rw [hmap2, map_mul, map_pow, map_prod, SX.exp_expExponent_mul_latticeSum]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_prod]
      exact Finset.prod_congr rfl fun j _ => by rw [map_pow, hVθ]
    have hVbK0 : V bK ≠ 0 := fun hcon => hbK0 (hVinj (by simpa using hcon))
    have hfac : (V bK) ^ T * ∑ lam : {lam : Fin d → ℕ // lam ∈ SX.box d L},
        ((t lam : ℤ) : ℂ) * Complex.exp (SX.expExponent x lam.1 * SX.latticeSum y m) = 0 := by
      rw [Finset.mul_sum, ← hVsum]
      exact Finset.sum_congr rfl fun lam _ => by rw [hVa lam]; ring
    have hzero : ∑ lam : {lam : Fin d → ℕ // lam ∈ SX.box d L},
        ((t lam : ℤ) : ℂ) * Complex.exp (SX.expExponent x lam.1 * SX.latticeSum y m) = 0 :=
      (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero _ hVbK0)
    rw [SX.expSum, ← Finset.sum_coe_sort (SX.box d L)
      (fun lam => ((pp lam : ℤ) : ℂ) * Complex.exp (SX.expExponent x lam * SX.latticeSum y m))]
    rw [← hzero]
    exact Finset.sum_congr rfl fun lam _ => by rw [hp lam]
