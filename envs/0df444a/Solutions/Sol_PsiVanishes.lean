-- Prove2me | solution 1 for PsiVanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:58:56.624774+00:00
-- url     : https://prove2.me/submissions/3d76c901-8079-436f-b964-c94c7c93cc99

import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Definitions.Def_Tablet_PsiVanishes
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiTildeMeasurable


set_option autoImplicit false
open MeasureTheory Filter Topology
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (D : Set E) (hDc : D.Countable) (hDne : D.Nonempty) (hDd : Dense D)
    (C : ℝ) (hC : 0 < C) (l : ℕ)
    (η : Measure (Curve E)) [IsFiniteMeasure η]
    (hlen : ∀ᵐ γ ∂η, γ.len = (l : ℝ))
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ (m : ℕ) (Q : Finset E) (ε : ℚ),
      1 ≤ m ∧ Q.Nonempty ∧ (Q : Set E) ⊆ D ∧ 0 < ε ∧
      Integrable (fun γ : Curve E => psi m Q (ε : ℝ) C γ) η ∧
      Integrable (fun γ : Curve E => psiTilde m Q (ε : ℝ) C γ) η ∧
      (∫ γ, psi m Q (ε : ℝ) C γ ∂η) + (∫ γ, psiTilde m Q (ε : ℝ) C γ ∂η) < θ := by
-- BODY
  -- ## Step 1: nonnegativity and the uniform dominator
  have hcard : ∀ k : ℕ, (Finset.Icc 1 k).card = k := by
    intro k; rw [Nat.card_Icc]; omega
  have sum_min_bounds : ∀ (k : ℕ) (A : ℝ) (B : ℕ → ℝ), 0 ≤ A → (∀ i, 0 ≤ B i) →
      0 ≤ ∑ i ∈ Finset.Icc 1 k, min A (B i) ∧
      (∑ i ∈ Finset.Icc 1 k, min A (B i)) ≤ (k : ℝ) * A := by
    intro k A B hA hB
    refine ⟨Finset.sum_nonneg fun i _ => le_min hA (hB i), ?_⟩
    calc ∑ i ∈ Finset.Icc 1 k, min A (B i) ≤ ∑ _i ∈ Finset.Icc 1 k, A :=
          Finset.sum_le_sum fun i _ => min_le_left _ _
      _ = (k:ℝ) * A := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hpb : ∀ (k : ℕ), 1 ≤ k → ∀ (Q : Finset E) (ε : ℝ), 0 ≤ ε → ∀ γ : Curve E,
      |psi k Q ε C γ| ≤ 2*C^2*γ.len + 2*C^2*γ.len^2 ∧
      |psiTilde k Q ε C γ| ≤ 2*C^2*γ.len + 2*C^2*γ.len^2 := by
    intro k hk Q ε hε γ
    have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hk0 : (0:ℝ) < (k:ℝ) := by linarith
    have hL : (0:ℝ) ≤ γ.len := γ.len_nonneg
    have hA : (0:ℝ) ≤ 2*C*γ.len/(k:ℝ) := div_nonneg (mul_nonneg (by linarith) hL) hk0.le
    have hdiv : 2*C^2*γ.len^2/(k:ℝ) ≤ 2*C^2*γ.len^2 := div_le_self (by positivity) hkR
    have hdiv0 : (0:ℝ) ≤ 2*C^2*γ.len^2/(k:ℝ) := by positivity
    have hmulk : (k:ℝ) * (2*C*γ.len/(k:ℝ)) = 2*C*γ.len := by field_simp
    have hbdnn : (0:ℝ) ≤ 2*C^2*γ.len + 2*C^2*γ.len^2 := by positivity
    constructor
    · obtain ⟨hs0, hs1⟩ := sum_min_bounds k (2*C*γ.len/(k:ℝ))
        (fun i => 2*ε + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E)
                          + Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(k:ℝ))) (Q : Set E)))
        hA (by
          intro i
          have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E) :=
            Metric.infDist_nonneg
          have h2 : (0:ℝ) ≤ Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(k:ℝ))) (Q : Set E) :=
            Metric.infDist_nonneg
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 2*C) (by linarith : (0:ℝ) ≤
            Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E)
            + Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(k:ℝ))) (Q : Set E))
          linarith)
      rw [hmulk] at hs1
      have hCs0 := mul_nonneg hC.le hs0
      have hCs1 : C * (∑ i ∈ Finset.Icc 1 k, min (2*C*γ.len/(k:ℝ))
          (2*ε + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E)
                    + Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(k:ℝ))) (Q : Set E)))) ≤ 2*C^2*γ.len := by
        nlinarith [hs1, hC.le]
      rw [abs_le]
      simp only [psi]
      constructor <;> nlinarith [hCs0, hCs1, hdiv, hdiv0, hbdnn]
    · obtain ⟨hs0, hs1⟩ := sum_min_bounds k (2*C)
        (fun i => ε + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E)))
        (by linarith) (by
          intro i
          have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E) :=
            Metric.infDist_nonneg
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 2*C) h1
          linarith)
      have hcoef : (0:ℝ) ≤ C*γ.len/(k:ℝ) := div_nonneg (mul_nonneg hC.le hL) hk0.le
      have hprod : C*γ.len/(k:ℝ) * (∑ i ∈ Finset.Icc 1 k, min (2*C)
          (ε + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E)))) ≤ 2*C^2*γ.len := by
        have h := mul_le_mul_of_nonneg_left hs1 hcoef
        have heq : C*γ.len/(k:ℝ) * ((k:ℝ) * (2*C)) = 2*C^2*γ.len := by field_simp
        linarith [h, heq.le, heq.ge]
      have hprod0 : (0:ℝ) ≤ C*γ.len/(k:ℝ) * (∑ i ∈ Finset.Icc 1 k, min (2*C)
          (ε + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(k:ℝ))) (Q : Set E)))) :=
        mul_nonneg hcoef hs0
      rw [abs_le]
      simp only [psiTilde]
      constructor <;> nlinarith [hprod, hprod0, hdiv, hdiv0, hbdnn]
  -- ## Step 1b: integrability, for every admissible (k, Q, ε)
  have hint : ∀ (k : ℕ), 1 ≤ k → ∀ (Q : Finset E) (ε : ℝ), 0 ≤ ε →
      Integrable (fun γ : Curve E => psi k Q ε C γ) η ∧
      Integrable (fun γ : Curve E => psiTilde k Q ε C γ) η := by
    intro k hk Q ε hε
    constructor
    · refine Integrable.mono' (integrable_const (2*C^2*(l:ℝ) + 2*C^2*(l:ℝ)^2))
        (PsiMeasurable k Q ε C).aestronglyMeasurable ?_
      filter_upwards [hlen] with γ hγ
      have h := (hpb k hk Q ε hε γ).1
      rw [hγ] at h
      simpa [Real.norm_eq_abs] using h
    · refine Integrable.mono' (integrable_const (2*C^2*(l:ℝ) + 2*C^2*(l:ℝ)^2))
        (PsiTildeMeasurable k Q ε C).aestronglyMeasurable ?_
      filter_upwards [hlen] with γ hγ
      have h := (hpb k hk Q ε hε γ).2
      rw [hγ] at h
      simpa [Real.norm_eq_abs] using h
  -- ## Step 3: enumerate D and build the increasing finite subsets
  classical
  obtain ⟨f, hf⟩ := hDc.exists_eq_range hDne
  obtain ⟨Qs, hQne, hQD, hQmem⟩ : ∃ Qs : ℕ → Finset E, (∀ N, (Qs N).Nonempty) ∧
      (∀ N, ((Qs N : Finset E) : Set E) ⊆ D) ∧ (∀ j N : ℕ, j ≤ N → f j ∈ Qs N) := by
    refine ⟨fun N => (Finset.range (N+1)).image f, ?_, ?_, ?_⟩
    · intro N
      exact ⟨f 0, Finset.mem_image_of_mem f (Finset.mem_range.mpr (Nat.succ_pos N))⟩
    · intro N x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨j, _, rfl⟩ := hx
      rw [hf]; exact Set.mem_range_self j
    · intro j N hjN
      exact Finset.mem_image_of_mem f (Finset.mem_range.mpr (by omega))
  obtain ⟨es, hes_pos, hesR⟩ : ∃ es : ℕ → ℚ, (∀ N, 0 < es N) ∧
      (∀ N : ℕ, ((es N : ℝ)) = 1/((N:ℝ)+1)) :=
    ⟨fun N => 1/((N:ℚ)+1), fun N => by positivity, fun N => by push_cast; ring⟩
  have hesnn : ∀ N : ℕ, (0:ℝ) ≤ ((es N : ℝ)) := by
    intro N; rw [hesR]; positivity
  have hesT : Tendsto (fun N : ℕ => ((es N : ℝ))) atTop (𝓝 0) := by
    simp only [hesR]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- ## Step 4: infDist to the finite sets tends to 0
  have hinfQ : ∀ x : E, Tendsto (fun N => Metric.infDist x ((Qs N : Finset E) : Set E))
      atTop (𝓝 0) := by
    intro x
    rw [Metric.tendsto_atTop]
    intro r hr
    obtain ⟨q, hqb, hqD⟩ := Metric.dense_iff.mp hDd x r hr
    rw [hf] at hqD
    obtain ⟨j, rfl⟩ := hqD
    refine ⟨j, fun N hN => ?_⟩
    have h1 : Metric.infDist x ((Qs N : Finset E) : Set E) ≤ dist x (f j) :=
      Metric.infDist_le_dist_of_mem (by exact_mod_cast hQmem j N hN)
    have h2 : dist x (f j) < r := by
      rw [dist_comm]; simpa [Metric.mem_ball] using hqb
    have h0 : (0:ℝ) ≤ Metric.infDist x ((Qs N : Finset E) : Set E) := Metric.infDist_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    linarith
  -- ## Step 2: fix m from θ
  obtain ⟨m, hm1, hkey⟩ : ∃ m : ℕ, 1 ≤ m ∧
      4*C^2*(l:ℝ)^2*(η Set.univ).toReal/(m:ℝ) < θ/2 := by
    set XX : ℝ := 4*C^2*(l:ℝ)^2*(η Set.univ).toReal with hXX
    have hXX0 : 0 ≤ XX := mul_nonneg (by positivity) ENNReal.toReal_nonneg
    refine ⟨max 1 (⌈2*XX/θ⌉₊ + 1), le_max_left _ _, ?_⟩
    set m : ℕ := max 1 (⌈2*XX/θ⌉₊ + 1) with hm_def
    have hm1 : 1 ≤ m := le_max_left _ _
    have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
    have h1 : (2*XX/θ : ℝ) ≤ (⌈2*XX/θ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2*XX/θ⌉₊ + 1 : ℕ) ≤ m := le_max_right _ _
    have h3 : ((⌈2*XX/θ⌉₊ : ℝ) + 1) ≤ (m:ℝ) := by exact_mod_cast h2
    have hmX : 2*XX/θ < (m:ℝ) := by linarith
    have h4 : 2*XX < (m:ℝ)*θ := (div_lt_iff₀ hθ).mp hmX
    rw [div_lt_iff₀ hmR]
    linarith
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
  -- ## Step 4b: pointwise convergence of ψ + ψ̃ along (Q_N, ε_N)
  have hptw : ∀ γ : Curve E, Tendsto (fun N => psi m (Qs N) ((es N : ℝ)) C γ
      + psiTilde m (Qs N) ((es N : ℝ)) C γ) atTop (𝓝 (4*C^2*γ.len^2/(m:ℝ))) := by
    intro γ
    have hL : (0:ℝ) ≤ γ.len := γ.len_nonneg
    have hA : (0:ℝ) ≤ 2*C*γ.len/(m:ℝ) := div_nonneg (mul_nonneg (by linarith) hL) hmR.le
    have hterm : ∀ i : ℕ, Tendsto (fun N => min (2*C*γ.len/(m:ℝ))
        (2*((es N : ℝ)) + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E))
          + Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(m:ℝ))) ((Qs N : Set E)))))
        atTop (𝓝 0) := by
      intro i
      have hB : Tendsto (fun N => 2*((es N : ℝ))
          + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E))
            + Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(m:ℝ))) ((Qs N : Set E))))
          atTop (𝓝 0) := by
        have h := (hesT.const_mul 2).add
          (((hinfQ (γ.toFun ((i:ℝ)*γ.len/(m:ℝ)))).add
            (hinfQ (γ.toFun (((i:ℝ)-1)*γ.len/(m:ℝ))))).const_mul (2*C))
        simpa using h
      refine squeeze_zero (fun N => le_min hA ?_) (fun N => min_le_right _ _) hB
      have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E)) :=
        Metric.infDist_nonneg
      have h2 : (0:ℝ) ≤ Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(m:ℝ))) ((Qs N : Set E)) :=
        Metric.infDist_nonneg
      have h3 := mul_nonneg (by linarith : (0:ℝ) ≤ 2*C) (by linarith :
        (0:ℝ) ≤ Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E))
          + Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(m:ℝ))) ((Qs N : Set E)))
      have h4 := hesnn N
      linarith
    have hterm' : ∀ i : ℕ, Tendsto (fun N => min (2*C)
        ((es N : ℝ) + 2*C*Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E))))
        atTop (𝓝 0) := by
      intro i
      have hB : Tendsto (fun N => (es N : ℝ)
          + 2*C*Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E)))
          atTop (𝓝 0) := by
        have h := hesT.add ((hinfQ (γ.toFun ((i:ℝ)*γ.len/(m:ℝ)))).const_mul (2*C))
        simpa using h
      refine squeeze_zero (fun N => le_min (by linarith) ?_) (fun N => min_le_right _ _) hB
      have h1 : (0:ℝ) ≤ Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E)) :=
        Metric.infDist_nonneg
      have h3 := mul_nonneg (by linarith : (0:ℝ) ≤ 2*C) h1
      have h4 := hesnn N
      linarith
    have hS : Tendsto (fun N => ∑ i ∈ Finset.Icc 1 m, min (2*C*γ.len/(m:ℝ))
        (2*((es N : ℝ)) + 2*C*(Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E))
          + Metric.infDist (γ.toFun (((i:ℝ)-1)*γ.len/(m:ℝ))) ((Qs N : Set E)))))
        atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.Icc 1 m)
        (fun i (_ : i ∈ Finset.Icc 1 m) => hterm i)
      simpa using h
    have hS' : Tendsto (fun N => ∑ i ∈ Finset.Icc 1 m, min (2*C)
        ((es N : ℝ) + 2*C*Metric.infDist (γ.toFun ((i:ℝ)*γ.len/(m:ℝ))) ((Qs N : Set E))))
        atTop (𝓝 0) := by
      have h := tendsto_finsetSum (Finset.Icc 1 m)
        (fun i (_ : i ∈ Finset.Icc 1 m) => hterm' i)
      simpa using h
    have main : Tendsto (fun N => psi m (Qs N) ((es N : ℝ)) C γ
        + psiTilde m (Qs N) ((es N : ℝ)) C γ) atTop
        (𝓝 ((C * 0 + 2*C^2*γ.len^2/(m:ℝ))
            + (2*C^2*γ.len^2/(m:ℝ) + C*γ.len/(m:ℝ) * 0))) := by
      simp only [psi, psiTilde]
      exact ((hS.const_mul C).add tendsto_const_nhds).add
        (tendsto_const_nhds.add (hS'.const_mul (C*γ.len/(m:ℝ))))
    have hval : ((C * 0 + 2*C^2*γ.len^2/(m:ℝ))
        + (2*C^2*γ.len^2/(m:ℝ) + C*γ.len/(m:ℝ) * 0)) = 4*C^2*γ.len^2/(m:ℝ) := by ring
    rw [hval] at main
    exact main
  -- ## Step 5: dominated convergence
  have hbddF : ∀ N : ℕ, ∀ᵐ γ ∂η,
      ‖psi m (Qs N) ((es N : ℝ)) C γ + psiTilde m (Qs N) ((es N : ℝ)) C γ‖
        ≤ 4*C^2*(l:ℝ) + 4*C^2*(l:ℝ)^2 := by
    intro N
    filter_upwards [hlen] with γ hγ
    obtain ⟨h1, h2⟩ := hpb m hm1 (Qs N) ((es N : ℝ)) (hesnn N) γ
    rw [hγ] at h1 h2
    have h3 := abs_add_le (psi m (Qs N) ((es N : ℝ)) C γ) (psiTilde m (Qs N) ((es N : ℝ)) C γ)
    rw [Real.norm_eq_abs]
    linarith
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := η)
      (F := fun N (γ : Curve E) => psi m (Qs N) ((es N : ℝ)) C γ
        + psiTilde m (Qs N) ((es N : ℝ)) C γ)
      (f := fun γ : Curve E => 4*C^2*γ.len^2/(m:ℝ))
      (fun _ => 4*C^2*(l:ℝ) + 4*C^2*(l:ℝ)^2)
      (fun N => ((PsiMeasurable m (Qs N) ((es N : ℝ)) C).add
        (PsiTildeMeasurable m (Qs N) ((es N : ℝ)) C)).aestronglyMeasurable)
      (integrable_const _) hbddF (Filter.Eventually.of_forall hptw)
  have hlimval : (∫ γ, 4*C^2*γ.len^2/(m:ℝ) ∂η)
      = 4*C^2*(l:ℝ)^2*(η Set.univ).toReal/(m:ℝ) := by
    rw [integral_congr_ae (g := fun _ : Curve E => 4*C^2*(l:ℝ)^2/(m:ℝ))
      (by filter_upwards [hlen] with γ hγ; rw [hγ])]
    rw [integral_const, smul_eq_mul, measureReal_def]
    ring
  rw [hlimval] at hDCT
  -- ## Step 6: extract a single N
  obtain ⟨N, hN⟩ := (hDCT.eventually_lt_const
    (show 4*C^2*(l:ℝ)^2*(η Set.univ).toReal/(m:ℝ) < θ by linarith)).exists
  -- ## Step 7: assemble the witness
  obtain ⟨hI1, hI2⟩ := hint m hm1 (Qs N) ((es N : ℝ)) (hesnn N)
  refine ⟨m, Qs N, es N, hm1, hQne N, hQD N, hes_pos N, hI1, hI2, ?_⟩
  rw [← integral_add hI1 hI2]
  exact hN
