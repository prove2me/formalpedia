-- Prove2me | solution 1 for SparseLpLq.SmallP.Supplement.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:08.664855+00:00
-- url     : https://prove2.me/submissions/bd829c13-02d2-4b16-88e8-2a9c668a5536

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Constants

open scoped ENNReal Matrix Topology

open SparseLpLq
open SparseLpLq.SmallP
open SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    ∀ p ∈ Set.Ioo (0 : ℝ) (pStar A b σ), SOL A b σ p 1 ⊆ SOL A b σ 0 1 := by
      classical
      intro p hp
      obtain ⟨hp0, hpS⟩ := hp
      have hpS1 : pStar A b σ ≤ 1 := by
        unfold pStar; split_ifs
        · exact le_refl _
        · exact min_le_left _ _
      have hp1 : p < 1 := lt_of_lt_of_le hpS hpS1
      have hpne : p ≠ 0 := ne_of_gt hp0
      have hq1 : ∀ v : Fin m → ℝ, qNorm 1 v = ∑ k, |v k| := by
        intro v; unfold qNorm; rw [PiLp.norm_eq_of_L1]; simp [Real.norm_eq_abs]
      have hq2 : ∀ v : Fin m → ℝ, qNorm 2 v = Real.sqrt (∑ k, v k ^ 2) := by
        intro v; unfold qNorm; rw [PiLp.norm_eq_of_L2]; simp [Real.norm_eq_abs, sq_abs]
      have hq21 : ∀ v : Fin m → ℝ, qNorm 2 v ≤ qNorm 1 v := by
        intro v
        rw [hq2, hq1]
        have h0 : 0 ≤ ∑ k, |v k| := Finset.sum_nonneg (fun k _ => abs_nonneg _)
        calc Real.sqrt (∑ k, v k ^ 2) ≤ Real.sqrt ((∑ k, |v k|) ^ 2) := by
              apply Real.sqrt_le_sqrt
              rw [sq, Finset.sum_mul]
              apply Finset.sum_le_sum
              intro i _
              rw [← sq_abs, sq]
              exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun k => |v k|)
                (fun k _ => abs_nonneg _) (Finset.mem_univ i)) (abs_nonneg _)
          _ = ∑ k, |v k| := Real.sqrt_sq h0
      have hqtri : ∀ u w : Fin m → ℝ, qNorm 2 (u + w) ≤ qNorm 2 u + qNorm 2 w := by
        intro u w; unfold qNorm; rw [WithLp.toLp_add]; exact norm_add_le _ _
      have h0inf : (0 : Fin n → ℝ) ∉ FEA A b σ 1 := by
        intro h
        simp only [FEA, Set.mem_setOf_eq, Matrix.mulVec_zero, zero_sub] at h
        have hb' := hb
        rw [hq1] at h hb'
        simp only [Pi.neg_apply, abs_neg] at h
        linarith
      have hlp0 : ∀ y : Fin n → ℝ, lpObj 0 y = ((Finset.univ.filter (fun i => y i ≠ 0)).card : ℝ) := by
        intro y; simp [lpObj]
      have hlpp : ∀ y : Fin n → ℝ, lpObj p y = ∑ i ∈ Finset.univ.filter (fun i => y i ≠ 0), |y i| ^ p := by
        intro y; rw [lpObj, if_neg hpne]
        rw [Finset.sum_filter_of_ne]
        intro i _ hi h; apply hi; rw [h, abs_zero, Real.zero_rpow hpne]
      have hSex : ∃ k : ℕ, ∃ y ∈ FEA A b σ 1, (Finset.univ.filter (fun i => y i ≠ 0)).card = k := by
        obtain ⟨y, hy⟩ := hfeas; exact ⟨_, y, hy, rfl⟩
      obtain ⟨y0, hy0, hy0k⟩ := Nat.find_spec hSex
      have hk0min : ∀ y ∈ FEA A b σ 1, Nat.find hSex ≤ (Finset.univ.filter (fun i => y i ≠ 0)).card := by
        intro y hy; exact Nat.find_min' hSex ⟨y, hy, rfl⟩
      set k0 := Nat.find hSex with hk0def
      have hsOpt : sOpt A b σ = (k0 : ℝ) := by
        unfold sOpt
        apply IsLeast.csInf_eq
        constructor
        · exact ⟨y0, hy0, by rw [hlp0, hy0k]⟩
        · rintro _ ⟨y, hy, rfl⟩
          rw [hlp0]; exact_mod_cast hk0min y hy
      have hk0pos : 1 ≤ k0 := by
        rw [Nat.one_le_iff_ne_zero]
        intro h
        rw [h, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hy0k
        apply h0inf
        have : y0 = 0 := by funext i; simpa using hy0k (Finset.mem_univ i)
        rw [← this]; exact hy0
      have hext : ∀ (I : Finset (Fin n)) (w : I → ℝ),
          A *ᵥ (fun i => if h : i ∈ I then w ⟨i, h⟩ else 0) = (Matrix.of fun i (j : I) => A i j) *ᵥ w := by
        intro I w
        funext k
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        rw [← Finset.sum_subset (Finset.subset_univ I) (by intro i _ hi; simp [hi])]
        rw [← Finset.sum_coe_sort I]
        apply Finset.sum_congr rfl
        intro j _
        simp
      obtain ⟨Bf, hBf⟩ : ∃ Bf : (I : Finset (Fin n)) → Matrix (Fin m) I ℝ,
          Bf = fun (I : Finset (Fin n)) => Matrix.of fun i (j : I) => A i (j : Fin n) := ⟨_, rfl⟩
      have hlam_def : lamHat A = sInf {μ : ℝ | ∃ I : Finset (Fin n), I.Nonempty ∧
          (Bf I).rank = I.card ∧ μ = sInf (spectrum ℝ ((Bf I)ᵀ * Bf I))} := by subst hBf; rfl
      have hext' : ∀ (I : Finset (Fin n)) (w : I → ℝ),
          A *ᵥ (fun i => if h : i ∈ I then w ⟨i, h⟩ else 0) = Bf I *ᵥ w := by
        intro I w; rw [hBf]; exact hext I w
      set J := Finset.univ.filter (fun i => y0 i ≠ 0) with hJdef
      have hJinj : Function.Injective (Bf J).mulVec := by
        intro c₁ c₂ heq
        by_contra hne
        have hc : ∃ j, c₁ j - c₂ j ≠ 0 := by
          by_contra h; push_neg at h; exact hne (funext fun j => sub_eq_zero.mp (h j))
        obtain ⟨j0, hj0⟩ := hc
        have hBc : Bf J *ᵥ (c₁ - c₂) = 0 := by
          rw [Matrix.mulVec_sub, heq, sub_self]
        have hAc' := hext' J (c₁ - c₂)
        rw [hBc] at hAc'
        set c' : Fin n → ℝ := fun i => if h : i ∈ J then (c₁ - c₂) ⟨i, h⟩ else 0 with hc'def
        set t := y0 j0 / (c₁ j0 - c₂ j0)
        set y1 := y0 - t • c' with hy1def
        have hy1 : y1 ∈ FEA A b σ 1 := by
          have : A *ᵥ y1 = A *ᵥ y0 := by
            rw [hy1def, Matrix.mulVec_sub, Matrix.mulVec_smul, hAc', smul_zero, sub_zero]
          show qNorm 1 (A *ᵥ y1 - b) ≤ σ
          rw [this]; exact hy0
        have hsub : Finset.univ.filter (fun i => y1 i ≠ 0) ⊆ J.erase j0 := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [Finset.mem_erase]
          constructor
          · intro hij; apply hi; subst hij
            simp only [hy1def, hc'def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dif_pos j0.2, t]
            rw [div_mul_cancel₀ _ hj0, sub_self]
          · by_contra hiJ'
            apply hi
            have : y0 i = 0 := by simpa [hJdef] using hiJ'
            simp [hy1def, hc'def, hiJ', this]
        have h1 := hk0min y1 hy1
        have h2 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem j0.2] at h2
        omega
      have hJrank : (Bf J).rank = J.card := by
        unfold Matrix.rank
        rw [LinearMap.finrank_range_of_inj hJinj]
        simp
      have hrank_inj : ∀ I : Finset (Fin n), (Bf I).rank = I.card → Function.Injective (Bf I).mulVec := by
        intro I hI
        have h := LinearMap.finrank_range_add_finrank_ker (Bf I).mulVecLin
        have h' : Module.finrank ℝ (LinearMap.range (Bf I).mulVecLin) = I.card := hI
        have h2 : Module.finrank ℝ (↥I → ℝ) = I.card := by simp
        have hker : LinearMap.ker (Bf I).mulVecLin = ⊥ := by
          rw [← Submodule.finrank_eq_zero]; omega
        exact LinearMap.ker_eq_bot.mp hker
      have hspec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix (Fin m) ι ℝ),
          (∀ w : ι → ℝ, sInf (spectrum ℝ (Bᵀ * B)) * (w ⬝ᵥ w) ≤ (B *ᵥ w) ⬝ᵥ (B *ᵥ w)) ∧
          (Nonempty ι → Function.Injective B.mulVec → 0 < sInf (spectrum ℝ (Bᵀ * B))) := by
        intro ι _ _ B
        have hT : Bᵀ * B = Bᴴ * B := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]
        have hH : (Bᵀ * B).IsHermitian := hT ▸ Matrix.isHermitian_conjTranspose_mul_self B
        have hfin : (spectrum ℝ (Bᵀ * B)).Finite := Matrix.finite_real_spectrum
        constructor
        · intro w
          set μ := sInf (spectrum ℝ (Bᵀ * B))
          have hle : ∀ x ∈ spectrum ℝ (Bᵀ * B), μ ≤ x := fun x hx => csInf_le hfin.bddBelow hx
          have hPSD : (Bᵀ * B - algebraMap ℝ (Matrix ι ι ℝ) μ).PosSemidef := by
            rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
            refine ⟨?_, ?_⟩
            · apply hH.sub
              simp [Matrix.IsHermitian, Matrix.algebraMap_eq_diagonal]
            · rw [← spectrum.sub_singleton_eq]
              rintro _ ⟨x, hx, y, hy, rfl⟩
              simp only [Set.mem_singleton_iff] at hy; subst hy
              simp only [Set.mem_setOf_eq, sub_nonneg]; exact hle x hx
          have h := hPSD.dotProduct_mulVec_nonneg w
          have h2 : w ⬝ᵥ ((Bᵀ * B) *ᵥ w) = (B *ᵥ w) ⬝ᵥ (B *ᵥ w) := by
            rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
          simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Algebra.algebraMap_eq_smul_one,
            Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at h
          linarith
        · intro hne hinj
          have hPD : (Bᵀ * B).PosDef := hT ▸ Matrix.PosDef.conjTranspose_mul_self B hinj
          have hspne : (spectrum ℝ (Bᵀ * B)).Nonempty := by
            rw [hH.spectrum_real_eq_range_eigenvalues]; exact Set.range_nonempty _
          have hmem := hspne.csInf_mem hfin
          obtain ⟨i, hi⟩ := (Set.ext_iff.mp hH.spectrum_real_eq_range_eigenvalues _).mp hmem
          rw [← hi]; exact hPD.eigenvalues_pos i
      have hlamfin : {μ : ℝ | ∃ I : Finset (Fin n), I.Nonempty ∧
          (Bf I).rank = I.card ∧ μ = sInf (spectrum ℝ ((Bf I)ᵀ * Bf I))}.Finite := by
        apply (Set.finite_range (fun I : Finset (Fin n) => sInf (spectrum ℝ ((Bf I)ᵀ * Bf I)))).subset
        rintro _ ⟨I, _, _, rfl⟩; exact ⟨I, rfl⟩
      have hJne : J.Nonempty := by rw [← Finset.card_pos, hy0k]; omega
      have hJmem : sInf (spectrum ℝ ((Bf J)ᵀ * Bf J)) ∈ {μ : ℝ | ∃ I : Finset (Fin n), I.Nonempty ∧
          (Bf I).rank = I.card ∧ μ = sInf (spectrum ℝ ((Bf I)ᵀ * Bf I))} := ⟨J, hJne, hJrank, rfl⟩
      have hlamle : lamHat A ≤ sInf (spectrum ℝ ((Bf J)ᵀ * Bf J)) := by
        rw [hlam_def]; exact csInf_le hlamfin.bddBelow hJmem
      have hlampos : 0 < lamHat A := by
        obtain ⟨I, hIne, hIr, hI⟩ := Set.Nonempty.csInf_mem ⟨_, hJmem⟩ hlamfin
        rw [hlam_def, hI]
        exact (hspec I (Bf I)).2 ⟨⟨_, hIne.choose_spec⟩⟩ (hrank_inj I hIr)
      have hy0bd : ∀ i, |y0 i| ≤ rConst A b σ := by
        intro i
        set z : J → ℝ := fun j => y0 j with hzdef
        have hAz : A *ᵥ y0 = Bf J *ᵥ z := by
          rw [← hext']; congr 1; funext i'
          by_cases h : i' ∈ J
          · simp [h, hzdef]
          · rw [dif_neg h]; simpa [hJdef] using h
        have hzz : y0 i ^ 2 ≤ z ⬝ᵥ z := by
          by_cases h : i ∈ J
          · have := Finset.single_le_sum (f := fun j : J => z j * z j) (fun j _ => mul_self_nonneg _)
              (Finset.mem_univ ⟨i, h⟩)
            simpa [dotProduct, sq, hzdef] using this
          · have : y0 i = 0 := by simpa [hJdef] using h
            rw [this, sq, zero_mul]
            exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
        have hR := (hspec J (Bf J)).1 z
        have h1 : lamHat A * y0 i ^ 2 ≤ (Bf J *ᵥ z) ⬝ᵥ (Bf J *ᵥ z) := by
          calc lamHat A * y0 i ^ 2 ≤ sInf (spectrum ℝ ((Bf J)ᵀ * Bf J)) * (z ⬝ᵥ z) :=
                mul_le_mul hlamle hzz (sq_nonneg _) (le_trans hlampos.le hlamle)
            _ ≤ _ := hR
        have h2 : Real.sqrt ((Bf J *ᵥ z) ⬝ᵥ (Bf J *ᵥ z)) = qNorm 2 (A *ᵥ y0) := by
          rw [hq2, hAz]; congr 1; simp [dotProduct, sq]
        have h3 : qNorm 2 (A *ᵥ y0) ≤ σ + qNorm 2 b := by
          have := hqtri (A *ᵥ y0 - b) b
          rw [sub_add_cancel] at this
          have h4 := hq21 (A *ᵥ y0 - b)
          have h5 : qNorm 1 (A *ᵥ y0 - b) ≤ σ := hy0
          linarith
        have h6 : |y0 i| * Real.sqrt (lamHat A) ≤ σ + qNorm 2 b := by
          rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), mul_comm]
          calc _ ≤ Real.sqrt ((Bf J *ᵥ z) ⬝ᵥ (Bf J *ᵥ z)) := Real.sqrt_le_sqrt h1
            _ ≤ _ := by rw [h2]; exact h3
        show |y0 i| ≤ (σ + qNorm 2 b) / Real.sqrt (lamHat A)
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hlampos)]; exact h6
      have hext_pt : ∀ x ∈ SOL A b σ p 1,
          x ∈ Set.extremePoints ℝ (orthant (fun i => decide (0 ≤ x i)) ∩ FEA A b σ 1) := by
        intro x hx
        rw [mem_extremePoints]
        have hxo : x ∈ orthant (fun i => decide (0 ≤ x i)) := by
          intro i; by_cases h : 0 ≤ x i
          · simp [h]
          · simp [h]; linarith
        refine ⟨⟨hxo, hx.1⟩, ?_⟩
        rintro x₁ ⟨hx₁o, hx₁f⟩ x₂ ⟨hx₂o, hx₂f⟩ ⟨a, c, ha, hc, hac, hxeq⟩
        have habs : ∀ i, |x i| = a * |x₁ i| + c * |x₂ i| := by
          intro i
          have e : x i = a * x₁ i + c * x₂ i := by rw [← hxeq]; simp
          have o1 := hx₁o i; have o2 := hx₂o i
          by_cases h : 0 ≤ x i
          · simp [h] at o1 o2
            rw [abs_of_nonneg h, abs_of_nonneg o1, abs_of_nonneg o2, e]
          · simp [h] at o1 o2
            rw [abs_of_neg (not_le.mp h), abs_of_nonpos o1, abs_of_nonpos o2, e]; ring
        have hconc := Real.strictConcaveOn_rpow hp0 hp1
        have hterm : ∀ i, a * |x₁ i| ^ p + c * |x₂ i| ^ p ≤ |x i| ^ p := by
          intro i; rw [habs i]
          exact hconc.concaveOn.2 (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _))
            ha.le hc.le hac
        have heqabs : ∀ i, |x₁ i| = |x₂ i| := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨i0, hi0⟩ := hcon
          have hstrict : a * |x₁ i0| ^ p + c * |x₂ i0| ^ p < |x i0| ^ p := by
            rw [habs i0]
            exact hconc.2 (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _)) hi0 ha hc hac
          have hsum : ∑ i, (a * |x₁ i| ^ p + c * |x₂ i| ^ p) < ∑ i, |x i| ^ p :=
            Finset.sum_lt_sum (fun i _ => hterm i) ⟨i0, Finset.mem_univ _, hstrict⟩
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
          have h1 := hx.2 x₁ hx₁f
          have h2 := hx.2 x₂ hx₂f
          simp only [lpObj, if_neg hpne] at h1 h2
          have e1 := mul_le_mul_of_nonneg_left h1 ha.le
          have e2 := mul_le_mul_of_nonneg_left h2 hc.le
          have e3 : a * ∑ i, |x i| ^ p + c * ∑ i, |x i| ^ p = ∑ i, |x i| ^ p := by
            rw [← add_mul, hac, one_mul]
          linarith
        have hx12 : x₁ = x₂ := by
          funext i
          have o1 := hx₁o i; have o2 := hx₂o i
          have := heqabs i
          by_cases h : 0 ≤ x i
          · simp [h] at o1 o2; rwa [abs_of_nonneg o1, abs_of_nonneg o2] at this
          · simp [h] at o1 o2; rw [abs_of_nonpos o1, abs_of_nonpos o2] at this; linarith
        subst hx12
        have : x = x₁ := by rw [← hxeq, ← add_smul, hac, one_smul]
        exact ⟨this.symm, this.symm⟩
      have hsignev : ∀ u v : ℝ, SignType.sign u = SignType.sign v →
          ∀ᶠ δ in 𝓝[>] (0:ℝ), SignType.sign ((1 + δ) * u - δ * v) = SignType.sign u := by
        intro u v huv
        have hT : Filter.Tendsto (fun δ : ℝ => (1 + δ) * u - δ * v) (𝓝[>] 0) (𝓝 u) := by
          have : Filter.Tendsto (fun δ : ℝ => (1 + δ) * u - δ * v) (𝓝 0) (𝓝 ((1 + 0) * u - 0 * v)) :=
            (((continuous_const.add continuous_id).mul continuous_const).sub
              (continuous_id.mul continuous_const)).tendsto 0
          simp only [add_zero, one_mul, zero_mul, sub_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        rcases lt_trichotomy u 0 with h | h | h
        · filter_upwards [hT.eventually (gt_mem_nhds h)] with δ hδ
          rw [sign_neg h, sign_neg hδ]
        · subst h
          have hv : v = 0 := by rw [sign_zero, eq_comm, sign_eq_zero_iff] at huv; exact huv
          subst hv
          filter_upwards with δ; simp
        · filter_upwards [hT.eventually (lt_mem_nhds h)] with δ hδ
          rw [sign_pos h, sign_pos hδ]
      have hkey : ∀ (s : Fin n → Bool) (x y : Fin n → ℝ),
          x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) → y ∈ FEA A b σ 1 →
          (∀ i, SignType.sign (x i) = SignType.sign (y i)) →
          (∀ k, SignType.sign ((A *ᵥ x - b) k) = SignType.sign ((A *ᵥ y - b) k)) →
          qNorm 1 (A *ᵥ x - b) ≤ qNorm 1 (A *ᵥ y - b) → x = y := by
        intro s x y hx hy hsx hsr hle
        by_contra hne
        rw [mem_extremePoints] at hx
        obtain ⟨⟨hxo, hxf⟩, hxe⟩ := hx
        have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧
            (∀ i, SignType.sign ((1 + δ) * x i - δ * y i) = SignType.sign (x i)) ∧
            (∀ k, SignType.sign ((1 + δ) * (A *ᵥ x - b) k - δ * (A *ᵥ y - b) k) =
              SignType.sign ((A *ᵥ x - b) k)) :=
          Filter.Eventually.and (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] 0)
            (Filter.Eventually.and (Filter.eventually_all.2 fun i => hsignev _ _ (hsx i))
              (Filter.eventually_all.2 fun k => hsignev _ _ (hsr k)))
        obtain ⟨δ, hδ, hδx, hδr⟩ := hev.exists
        set x₁ : Fin n → ℝ := (1 + δ) • x - δ • y with hx₁
        have hr₁ : A *ᵥ x₁ - b = (1 + δ) • (A *ᵥ x - b) - δ • (A *ᵥ y - b) := by
          rw [hx₁, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
          funext k; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        have hyo : y ∈ orthant s := by
          intro i; have := hxo i
          split_ifs at this ⊢
          · rw [← sign_nonneg_iff, ← hsx i, sign_nonneg_iff]; exact this
          · rw [← sign_nonpos_iff, ← hsx i, sign_nonpos_iff]; exact this
        have hx₁o : x₁ ∈ orthant s := by
          intro i; have := hxo i
          have e : x₁ i = (1 + δ) * x i - δ * y i := by simp [hx₁]
          split_ifs at this ⊢
          · rw [← sign_nonneg_iff, e, hδx i, sign_nonneg_iff]; exact this
          · rw [← sign_nonpos_iff, e, hδx i, sign_nonpos_iff]; exact this
        have hx₁f : x₁ ∈ FEA A b σ 1 := by
          show qNorm 1 (A *ᵥ x₁ - b) ≤ σ
          rw [hr₁, hq1]
          have : ∀ k, |((1 + δ) • (A *ᵥ x - b) - δ • (A *ᵥ y - b)) k| =
              (1 + δ) * |(A *ᵥ x - b) k| - δ * |(A *ᵥ y - b) k| := by
            intro k
            show |(1 + δ) * (A *ᵥ x - b) k - δ * (A *ᵥ y - b) k| = _
            rw [← self_mul_sign, hδr k, ← self_mul_sign ((A *ᵥ x - b) k),
              ← self_mul_sign ((A *ᵥ y - b) k), ← hsr k]; ring
          simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
          have hxf' : qNorm 1 (A *ᵥ x - b) ≤ σ := hxf
          rw [hq1, hq1] at hle; rw [hq1] at hxf'
          nlinarith
        have hseg : x ∈ openSegment ℝ x₁ y := by
          refine ⟨1 / (1 + δ), δ / (1 + δ), by positivity, by positivity, by field_simp, ?_⟩
          rw [hx₁]; funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          field_simp; ring
        have := hxe x₁ ⟨hx₁o, hx₁f⟩ y ⟨hyo, hy⟩ hseg
        exact hne this.2.symm
      have hTfin : {t : ℝ | ∃ (s : Fin n → Bool) (x : Fin n → ℝ) (i : Fin n),
          x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) ∧ x i ≠ 0 ∧ t = |x i|}.Finite := by
        have hEfin : {x : Fin n → ℝ | ∃ s : Fin n → Bool,
            x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1)}.Finite := by
          apply Set.Finite.of_finite_image (f := fun x : Fin n → ℝ =>
            ((fun i => SignType.sign (x i)), (fun k => SignType.sign ((A *ᵥ x - b) k))))
            (Set.finite_univ.subset (Set.subset_univ _))
          rintro x ⟨s, hxs⟩ y ⟨s', hys⟩ hxy
          simp only [Prod.mk.injEq] at hxy
          obtain ⟨h1, h2⟩ := hxy
          have hxf : x ∈ FEA A b σ 1 := hxs.1.2
          have hyf : y ∈ FEA A b σ 1 := hys.1.2
          rcases le_total (qNorm 1 (A *ᵥ x - b)) (qNorm 1 (A *ᵥ y - b)) with hle | hle
          · exact hkey s x y hxs hyf (fun i => congrFun h1 i) (fun k => congrFun h2 k) hle
          · exact (hkey s' y x hys hxf (fun i => (congrFun h1 i).symm)
              (fun k => (congrFun h2 k).symm) hle).symm
        apply ((hEfin.prod (Set.finite_univ (α := Fin n))).image
          (fun xi : (Fin n → ℝ) × Fin n => |xi.1 xi.2|)).subset
        rintro t ⟨s, x, i, hx, hxi, rfl⟩
        exact ⟨(x, i), ⟨⟨s, hx⟩, Set.mem_univ _⟩, rfl⟩
      have hrt_def : rTilde A b σ = sInf {t : ℝ | ∃ (s : Fin n → Bool) (x : Fin n → ℝ) (i : Fin n),
          x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) ∧ x i ≠ 0 ∧ t = |x i|} := rfl
      intro x hx
      have hxe := hext_pt x hx
      have hxne : ∃ i, x i ≠ 0 := by
        by_contra h; push_neg at h; apply h0inf; have : x = 0 := funext h; rw [← this]; exact hx.1
      obtain ⟨i0, hi0⟩ := hxne
      have hTmem : ∀ i, x i ≠ 0 → |x i| ∈ {t : ℝ | ∃ (s : Fin n → Bool) (x : Fin n → ℝ) (i : Fin n),
          x ∈ Set.extremePoints ℝ (orthant s ∩ FEA A b σ 1) ∧ x i ≠ 0 ∧ t = |x i|} :=
        fun i hi => ⟨_, x, i, hxe, hi, rfl⟩
      have hrt_le : ∀ i, x i ≠ 0 → rTilde A b σ ≤ |x i| := fun i hi => by
        rw [hrt_def]; exact csInf_le hTfin.bddBelow (hTmem i hi)
      have hrt_pos : 0 < rTilde A b σ := by
        obtain ⟨s, x', i, _, hxi, ht⟩ := Set.Nonempty.csInf_mem ⟨_, hTmem i0 hi0⟩ hTfin
        rw [hrt_def, ht]; exact abs_pos.mpr hxi
      have hr_nonneg : 0 ≤ rConst A b σ := le_trans (abs_nonneg _) (hy0bd i0)
      have hck : (Finset.univ.filter (fun i => x i ≠ 0)).card ≤ k0 := by
        by_contra hcon
        push_neg at hcon
        have hlx : ((k0:ℝ) + 1) * rTilde A b σ ^ p ≤ lpObj p x := by
          rw [hlpp]
          calc ((k0:ℝ) + 1) * rTilde A b σ ^ p
              ≤ ((Finset.univ.filter (fun i => x i ≠ 0)).card : ℝ) * rTilde A b σ ^ p := by
                apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hrt_pos.le _)
                exact_mod_cast hcon
            _ = ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), rTilde A b σ ^ p := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum fun i hi =>
                Real.rpow_le_rpow hrt_pos.le (hrt_le i (Finset.mem_filter.1 hi).2) hp0.le
        have hly : lpObj p y0 ≤ (k0:ℝ) * rConst A b σ ^ p := by
          rw [hlpp]
          calc _ ≤ ∑ i ∈ J, rConst A b σ ^ p :=
                Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _) (hy0bd i) hp0.le
            _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hy0k]
        have hxy := hx.2 y0 hy0
        have hmain : (k0:ℝ) * rConst A b σ ^ p < ((k0:ℝ) + 1) * rTilde A b σ ^ p := by
          have hk0r : (0:ℝ) < k0 := by exact_mod_cast hk0pos
          rcases le_or_gt (rConst A b σ) (rTilde A b σ) with hle | hlt
          · calc (k0:ℝ) * rConst A b σ ^ p ≤ k0 * rTilde A b σ ^ p :=
                  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr_nonneg hle hp0.le) hk0r.le
              _ < _ := by have := Real.rpow_pos_of_pos hrt_pos p; linarith
          · have hne : rConst A b σ ≠ rTilde A b σ := ne_of_gt hlt
            have hrpos : 0 < rConst A b σ := lt_trans hrt_pos hlt
            have hD : 0 < Real.log (rConst A b σ) - Real.log (rTilde A b σ) :=
              sub_pos.mpr (Real.log_lt_log hrt_pos hlt)
            have hpQ : p < (Real.log ((k0:ℝ) + 1) - Real.log k0) /
                (Real.log (rConst A b σ) - Real.log (rTilde A b σ)) := by
              have := hpS; unfold pStar at this; rw [if_neg hne, hsOpt] at this
              exact lt_of_lt_of_le this (min_le_right _ _)
            rw [lt_div_iff₀ hD] at hpQ
            have hA1 := Real.rpow_pos_of_pos hrpos p
            have hA2 := Real.rpow_pos_of_pos hrt_pos p
            rw [← Real.log_lt_log_iff (mul_pos hk0r hA1) (mul_pos (by linarith) hA2)]
            rw [Real.log_mul hk0r.ne' hA1.ne', Real.log_mul (by linarith) hA2.ne',
              Real.log_rpow hrpos, Real.log_rpow hrt_pos]
            nlinarith
        linarith
      refine ⟨hx.1, fun z hz => ?_⟩
      rw [hlp0, hlp0]
      exact_mod_cast le_trans hck (hk0min z hz)
