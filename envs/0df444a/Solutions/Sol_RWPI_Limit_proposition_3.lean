-- Prove2me | solution 1 for RWPI.Limit.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:19:30.458877+00:00
-- url     : https://prove2.me/submissions/50430551-81d4-418b-b4d7-fee43d84dafe

import Mathlib
import Definitions.Def_RWPI_Limit_rwp
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution

set_option autoImplicit false

open MeasureTheory RWPI.Limit RWPI.SqrtLasso WassersteinDRO.Regularization
open scoped ENNReal

namespace SolRWPILimitProp3

private noncomputable def evalFS {α E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : α → E) : (α →₀ ℝ) →ₗ[ℝ] E :=
  Finsupp.lsum ℝ (fun u => LinearMap.toSpanSingleton ℝ E (f u))

private lemma evalFS_apply {α E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : α → E) (p : α →₀ ℝ) :
    evalFS f p = ∑ u ∈ p.support, p u • f u := by
  simp [evalFS, Finsupp.lsum, Finsupp.sum]

private lemma evalFS_single {α E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : α → E) (u : α) (a : ℝ) :
    evalFS f (Finsupp.single u a) = a • f u := by
  simp [evalFS]

private def IsProbFS {m : ℕ} (p : (Fin m → ℝ) →₀ ℝ) : Prop :=
  (∀ u, 0 ≤ p u) ∧ evalFS (fun _ => (1 : ℝ)) p = 1

private lemma isProbFS_single {m : ℕ} (u : Fin m → ℝ) :
    IsProbFS (Finsupp.single u (1 : ℝ)) := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [evalFS_single, smul_eq_mul, mul_one]

private lemma isProbFS_finset_sum {m : ℕ} {κ : Type*} (s : Finset κ) (wt : κ → ℝ)
    (p : κ → ((Fin m → ℝ) →₀ ℝ)) (hwt_nn : ∀ k ∈ s, 0 ≤ wt k) (hwt_sum : ∑ k ∈ s, wt k = 1)
    (hp : ∀ k ∈ s, IsProbFS (p k)) :
    IsProbFS (∑ k ∈ s, wt k • p k) := by
  refine ⟨fun u => ?_, ?_⟩
  · rw [Finsupp.finsetSum_apply]
    refine Finset.sum_nonneg fun k hk => ?_
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact mul_nonneg (hwt_nn k hk) ((hp k hk).1 u)
  · rw [map_sum]
    calc ∑ k ∈ s, evalFS (fun _ => (1 : ℝ)) (wt k • p k)
        = ∑ k ∈ s, wt k * evalFS (fun _ => (1 : ℝ)) (p k) := by
          refine Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]
      _ = ∑ k ∈ s, wt k := by
          refine Finset.sum_congr rfl fun k hk => by rw [(hp k hk).2, mul_one]
      _ = 1 := hwt_sum

private lemma isProbFS_convex_comb {m : ℕ} {p q : (Fin m → ℝ) →₀ ℝ}
    (hp : IsProbFS p) (hq : IsProbFS q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsProbFS (a • p + b • q) := by
  refine ⟨fun u => ?_, ?_⟩
  · simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 u)) (mul_nonneg hb (hq.1 u))
  · rw [map_add, map_smul, map_smul, hp.2, hq.2, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hab]

private lemma exists_isProbFS_of_mem_convexHull {m r : ℕ} (g : (Fin m → ℝ) → (Fin r → ℝ))
    {y : Fin r → ℝ} (hy : y ∈ convexHull ℝ (Set.range g)) :
    ∃ p : (Fin m → ℝ) →₀ ℝ, IsProbFS p ∧ evalFS g p = y := by
  obtain ⟨κ, hfin, wt, z, hwt_nn, hwt_sum, hz_mem, hz_sum⟩ :=
    mem_convexHull_iff_exists_fintype.mp hy
  let _ : Fintype κ := hfin
  choose u hu using hz_mem
  refine ⟨∑ k : κ, wt k • Finsupp.single (u k) (1 : ℝ),
    isProbFS_finset_sum Finset.univ wt (fun k => Finsupp.single (u k) 1)
      (fun k _ => hwt_nn k) hwt_sum (fun k _ => isProbFS_single (u k)), ?_⟩
  rw [map_sum]
  simp_rw [map_smul, evalFS_single, one_smul, hu]
  exact hz_sum

private noncomputable def meanH {m r n : ℕ} (g : (Fin m → ℝ) → (Fin r → ℝ)) :
    (Fin n → ((Fin m → ℝ) →₀ ℝ)) →ₗ[ℝ] (Fin r → ℝ) where
  toFun P := (1 / (n : ℝ)) • ∑ i : Fin n, evalFS g (P i)
  map_add' P Q := by simp [Finset.sum_add_distrib, smul_add]
  map_smul' a P := by simp [Finset.smul_sum, smul_smul, mul_comm]

private noncomputable def meanC {m n : ℕ} (c : (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞)
    (w : Fin n → (Fin m → ℝ)) :
    (Fin n → ((Fin m → ℝ) →₀ ℝ)) →ₗ[ℝ] ℝ where
  toFun P := (1 / (n : ℝ)) * ∑ i : Fin n, evalFS (fun u => (c u (w i)).toReal) (P i)
  map_add' P Q := by simp [Finset.sum_add_distrib, mul_add]
  map_smul' a P := by
    dsimp
    have hsum : ∑ i : Fin n, evalFS (fun u => (c u (w i)).toReal) (a • P i) =
        a * ∑ i : Fin n, evalFS (fun u => (c u (w i)).toReal) (P i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    rw [hsum]
    ring

private lemma meanC_nonneg {m n : ℕ} (c : (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞)
    (w : Fin n → (Fin m → ℝ)) {P : Fin n → ((Fin m → ℝ) →₀ ℝ)}
    (hP : ∀ i, IsProbFS (P i)) :
    0 ≤ meanC c w P := by
  simp only [meanC, LinearMap.coe_mk, AddHom.coe_mk, evalFS_apply, smul_eq_mul]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
  refine Finset.sum_nonneg fun u _ => ?_
  exact mul_nonneg ((hP i).1 u) ENNReal.toReal_nonneg

private lemma rwp_le_meanC {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (c : (Fin m → ℝ) → (Fin m → ℝ) → ℝ≥0∞)
    (hc_lsc : LowerSemicontinuous (Function.uncurry c)) (hc_fin : ∀ u v, c u v ≠ ⊤)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (P : Fin n → ((Fin m → ℝ) →₀ ℝ)) (hP : ∀ i, IsProbFS (P i))
    (hP_zero : meanH (fun u => h u θ) P = 0) :
    rwp c h θ (empiricalDistribution w) ≤ ENNReal.ofReal (meanC c w P) := by
  have hn_ne0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hsum_wt : ∀ i : Fin n, ∑ u ∈ (P i).support, ENNReal.ofReal (P i u) = 1 := by
    intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => (hP i).1 u)]
    have h1 : ∑ u ∈ (P i).support, P i u = 1 := by
      have := (hP i).2
      rwa [evalFS_apply, ← Finset.sum_smul, smul_eq_mul, mul_one] at this
    rw [h1, ENNReal.ofReal_one]
  set μP : Measure (Fin m → ℝ) :=
    (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, ∑ u ∈ (P i).support, ENNReal.ofReal (P i u) • Measure.dirac u
  set πP : Measure ((Fin m → ℝ) × (Fin m → ℝ)) :=
    (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, ∑ u ∈ (P i).support,
      ENNReal.ofReal (P i u) • Measure.dirac (u, w i)
  have hπ_prob : IsProbabilityMeasure πP := by
    refine ⟨?_⟩
    simp only [πP, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, hsum_wt,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel hn_ne0 hn_ne_top
  have hπ_fst : πP.map Prod.fst = μP := by
    ext S hS
    rw [Measure.map_apply measurable_fst hS]
    simp only [πP, μP, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      Measure.dirac_apply' _ (hS.preimage measurable_fst), Measure.dirac_apply' _ hS]
    rfl
  have hπ_snd : πP.map Prod.snd = empiricalDistribution w := by
    ext S hS
    rw [Measure.map_apply measurable_snd hS]
    simp only [πP, empiricalDistribution, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdir : ∀ u : Fin m → ℝ,
        Measure.dirac (u, w i) (Prod.snd ⁻¹' S) = Measure.dirac (w i) S := fun u => by
      rw [Measure.dirac_apply' _ (hS.preimage measurable_snd), Measure.dirac_apply' _ hS]
      rfl
    simp_rw [hdir, ← Finset.sum_mul, hsum_wt i, one_mul]
  have hμ_prob : IsProbabilityMeasure μP := by
    rw [← hπ_fst]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hμ_int : Integrable (fun u => h u θ) μP := by
    dsimp [μP]
    refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr hn_ne0)
    refine integrable_finsetSum_measure.mpr fun i _ => ?_
    refine integrable_finsetSum_measure.mpr fun u _ => ?_
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hμ_mean : ∫ u, h u θ ∂μP = 0 := by
    have hcalc : ∫ u, h u θ ∂μP = meanH (fun u => h u θ) P := by
      simp only [μP, meanH, LinearMap.coe_mk, AddHom.coe_mk, evalFS_apply]
      rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_eq_one_div,
        integral_finsetSum_measure (fun i _ => integrable_finsetSum_measure.mpr fun u _ =>
          (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum_measure (fun u _ =>
        (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ((hP i).1 u)]
    rw [hcalc, hP_zero]
  have hcost_π : ∫⁻ z, c z.1 z.2 ∂πP = ENNReal.ofReal (meanC c w P) := by
    dsimp [πP]
    rw [lintegral_smul_measure, lintegral_finsetSum_measure]
    have hinner : ∀ i : Fin n,
        ∫⁻ z, c z.1 z.2 ∂(∑ u ∈ (P i).support, ENNReal.ofReal (P i u) • Measure.dirac (u, w i)) =
        ENNReal.ofReal (evalFS (fun u => (c u (w i)).toReal) (P i)) := by
      intro i
      rw [lintegral_finsetSum_measure, evalFS_apply]
      simp only [smul_eq_mul]
      rw [ENNReal.ofReal_sum_of_nonneg (fun u _ => mul_nonneg ((hP i).1 u) ENNReal.toReal_nonneg)]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hdirac : ∫⁻ z, c z.1 z.2 ∂Measure.dirac (u, w i) = c u (w i) :=
        lintegral_dirac' (u, w i)
          (hc_lsc.measurable : Measurable fun z : (Fin m → ℝ) × (Fin m → ℝ) => c z.1 z.2)
      rw [lintegral_smul_measure, hdirac,
        ENNReal.ofReal_mul ((hP i).1 u), ENNReal.ofReal_toReal (hc_fin u (w i)), smul_eq_mul]
    simp_rw [hinner]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      rw [evalFS_apply]
      exact Finset.sum_nonneg fun u _ => mul_nonneg ((hP i).1 u) ENNReal.toReal_nonneg)]
    dsimp [meanC]
    have hn_inv : (n : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (n : ℝ)) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr hn), ENNReal.ofReal_natCast]
    rw [hn_inv, ← ENNReal.ofReal_mul (by positivity)]
  calc rwp c h θ (empiricalDistribution w)
      ≤ transportCost c μP (empiricalDistribution w) :=
        iInf₂_le μP ⟨hμ_prob, hμ_int, hμ_mean⟩
    _ ≤ ∫⁻ z, c z.1 z.2 ∂πP :=
        iInf₂_le πP ⟨hπ_prob, hπ_fst, hπ_snd⟩
    _ = ENNReal.ofReal (meanC c w P) := hcost_π

private lemma ereal_add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ := by
  cases x <;> cases y <;> simp_all

private lemma finset_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ereal_add_ne_bot (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma finset_sum_coe_ereal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, ((f i : ℝ) : EReal) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

private lemma coe_real_le_ennreal_toEReal (d : ℝ) {x : ℝ≥0∞} (h : ENNReal.ofReal d ≤ x) :
    ((d : ℝ) : EReal) ≤ (x : EReal) := by
  rcases le_or_gt d 0 with hd | hd
  · exact (EReal.coe_le_coe_iff.mpr hd).trans (EReal.coe_ennreal_nonneg x)
  · have hd_eq : ((d : ℝ) : EReal) = (ENNReal.ofReal d : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left hd.le]
    rw [hd_eq]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr h

end SolRWPILimitProp3

theorem solution {m l r n : ℕ} (hn : 0 < n) (w : Fin n → (Fin m → ℝ))
    (hw : Function.Injective w)
    (c : (Fin m → ℝ) → (Fin m → ℝ) → ENNReal)
    (hc_lsc : LowerSemicontinuous (Function.uncurry c))
    (hc_diag : ∀ u, c u u = 0) (hc_fin : ∀ u v, c u v ≠ ⊤)
    (h : (Fin m → ℝ) → (Fin l → ℝ) → (Fin r → ℝ)) (θ : Fin l → ℝ)
    (hmeas : Measurable fun u => h u θ)
    (hint : (0 : Fin r → ℝ) ∈ interior (convexHull ℝ (Set.range fun u => h u θ))) :
    (rwp c h θ (WassersteinDRO.Regularization.empiricalDistribution w) : EReal) =
      ⨆ lam : Fin r → ℝ, -(((1 / (n : ℝ) : ℝ) : EReal) *
        ∑ i, ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u (w i) : EReal))) := by
  have _ := hw
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  set Pn := empiricalDistribution w
  set R := rwp c h θ Pn
  set φ : (Fin r → ℝ) → (Fin m → ℝ) → EReal := fun lam v =>
    ⨆ u : Fin m → ℝ, (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u v : EReal))
  have hφ_sub : ∀ (lam : Fin r → ℝ) (u v : Fin m → ℝ),
      (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u v : EReal)) =
        (((lam ⬝ᵥ h u θ - (c u v).toReal : ℝ) : EReal)) := by
    intro lam u v
    have hcv : (c u v : EReal) = (((c u v).toReal : ℝ) : EReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal (hc_fin u v)]
      rw [EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
    rw [hcv, ← EReal.coe_sub]
  have hφ_ne_bot : ∀ (lam : Fin r → ℝ) (v : Fin m → ℝ), φ lam v ≠ ⊥ := by
    intro lam v
    have hle : (((lam ⬝ᵥ h v θ : ℝ) : EReal) - (c v v : EReal)) ≤ φ lam v :=
      le_iSup (fun u : Fin m → ℝ => (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u v : EReal))) v
    rw [hc_diag v] at hle
    have hbot : (((lam ⬝ᵥ h v θ : ℝ) : EReal) - (0 : ℝ≥0∞)) ≠ ⊥ := by simp
    intro h_eq
    rw [h_eq] at hle
    exact hbot (le_bot_iff.mp hle)
  apply le_antisymm
  · -- Strong duality: LHS ≤ RHS via convex separation in ℝ^r × ℝ
    have h0_ch : (0 : Fin r → ℝ) ∈ convexHull ℝ (Set.range fun u => h u θ) :=
      interior_subset hint
    obtain ⟨q0, hq0_prob, hq0_mean⟩ :=
      SolRWPILimitProp3.exists_isProbFS_of_mem_convexHull (fun u => h u θ) h0_ch
    set P0 : Fin n → ((Fin m → ℝ) →₀ ℝ) := fun _ => q0
    have hP0_prob : ∀ i, SolRWPILimitProp3.IsProbFS (P0 i) := fun _ => hq0_prob
    have hP0_zero : SolRWPILimitProp3.meanH (fun u => h u θ) P0 = 0 := by
      simp [SolRWPILimitProp3.meanH, P0, hq0_mean]
    have hR_le_P0 : R ≤ ENNReal.ofReal (SolRWPILimitProp3.meanC c w P0) :=
      SolRWPILimitProp3.rwp_le_meanC hn w c hc_lsc hc_fin h θ P0 hP0_prob hP0_zero
    have hR_lt_top : R < ⊤ := hR_le_P0.trans_lt ENNReal.ofReal_lt_top
    set α_opt : ℝ := R.toReal
    have hα_nonneg : 0 ≤ α_opt := ENNReal.toReal_nonneg
    have hR_ereal : (R : EReal) = ((α_opt : ℝ) : EReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hR_lt_top.ne]
      rw [EReal.coe_ennreal_ofReal, max_eq_left hα_nonneg]
    set K : Set ((Fin r → ℝ) × ℝ) := {yt | ∃ P : Fin n → ((Fin m → ℝ) →₀ ℝ),
      (∀ i, SolRWPILimitProp3.IsProbFS (P i)) ∧
      SolRWPILimitProp3.meanH (fun u => h u θ) P = yt.1 ∧
      SolRWPILimitProp3.meanC c w P < yt.2}
    have hK_conv : Convex ℝ K := by
      rintro ⟨y1, t1⟩ ⟨P1, hP1, hy1, ht1⟩ ⟨y2, t2⟩ ⟨P2, hP2, hy2, ht2⟩ a b ha hb hab
      refine ⟨a • P1 + b • P2,
        fun i => SolRWPILimitProp3.isProbFS_convex_comb (hP1 i) (hP2 i) ha hb hab, ?_, ?_⟩
      · simp [map_add, map_smul, hy1, hy2]
      · simp only [map_add, map_smul, smul_eq_mul, Prod.smul_snd, Prod.snd_add]
        rcases ha.eq_or_lt with rfl | ha_pos
        · simp only [zero_add] at hab; subst hab; linarith
        · nlinarith
    have hnot_mem : ((0 : Fin r → ℝ), α_opt) ∉ K := by
      rintro ⟨P, hP_prob, hP_zero, hP_lt⟩
      have hle : R ≤ ENNReal.ofReal (SolRWPILimitProp3.meanC c w P) :=
        SolRWPILimitProp3.rwp_le_meanC hn w c hc_lsc hc_fin h θ P hP_prob hP_zero
      have hnn : 0 ≤ SolRWPILimitProp3.meanC c w P :=
        SolRWPILimitProp3.meanC_nonneg c w hP_prob
      have hle_real : α_opt ≤ SolRWPILimitProp3.meanC c w P := by
        have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
        rwa [ENNReal.toReal_ofReal hnn] at h1
      linarith
    obtain ⟨δ₀, hδ₀_pos, hball_sub⟩ :=
      Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
    set δ₁ : ℝ := δ₀ / 2
    have hδ₁_pos : 0 < δ₁ := half_pos hδ₀_pos
    have hpos_ch : ∀ j : Fin r,
        δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ) ∈ convexHull ℝ (Set.range fun u => h u θ) := by
      intro j
      apply hball_sub
      rw [Metric.mem_ball, dist_zero_right]
      have hnorm : ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
        rw [Pi.single_apply]; split_ifs <;> simp
      calc ‖δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)‖
          = δ₁ * ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ₁_pos]
        _ ≤ δ₁ * 1 := mul_le_mul_of_nonneg_left hnorm hδ₁_pos.le
        _ < δ₀ := by dsimp [δ₁]; linarith
    have hneg_ch : ∀ j : Fin r,
        -(δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)) ∈ convexHull ℝ (Set.range fun u => h u θ) := by
      intro j
      apply hball_sub
      rw [Metric.mem_ball, dist_zero_right, norm_neg]
      have hnorm : ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun k => ?_
        rw [Pi.single_apply]; split_ifs <;> simp
      calc ‖δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)‖
          = δ₁ * ‖(Pi.single j (1 : ℝ) : Fin r → ℝ)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ₁_pos]
        _ ≤ δ₁ * 1 := mul_le_mul_of_nonneg_left hnorm hδ₁_pos.le
        _ < δ₀ := by dsimp [δ₁]; linarith
    choose q_pos hq_pos_prob hq_pos_mean using fun j =>
      SolRWPILimitProp3.exists_isProbFS_of_mem_convexHull (fun u => h u θ) (hpos_ch j)
    choose q_neg hq_neg_prob hq_neg_mean using fun j =>
      SolRWPILimitProp3.exists_isProbFS_of_mem_convexHull (fun u => h u θ) (hneg_ch j)
    set P_pos : Fin r → Fin n → ((Fin m → ℝ) →₀ ℝ) := fun j _ => q_pos j
    set P_neg : Fin r → Fin n → ((Fin m → ℝ) →₀ ℝ) := fun j _ => q_neg j
    have hP_pos_mean : ∀ j : Fin r, SolRWPILimitProp3.meanH (fun u => h u θ) (P_pos j) =
        δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ) := fun j => by
      ext k
      simp only [SolRWPILimitProp3.meanH, LinearMap.coe_mk, AddHom.coe_mk, P_pos, hq_pos_mean j,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hn_pos.ne']
    have hP_neg_mean : ∀ j : Fin r, SolRWPILimitProp3.meanH (fun u => h u θ) (P_neg j) =
        -(δ₁ • (Pi.single j (1 : ℝ) : Fin r → ℝ)) := fun j => by
      ext k
      simp only [SolRWPILimitProp3.meanH, LinearMap.coe_mk, AddHom.coe_mk, P_neg, hq_neg_mean j,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.mul_apply,
        Pi.natCast_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      field_simp [hn_pos.ne']
    have hC0_nn : 0 ≤ SolRWPILimitProp3.meanC c w P0 :=
      SolRWPILimitProp3.meanC_nonneg c w hP0_prob
    have hCpos_nn : ∀ j : Fin r, 0 ≤ SolRWPILimitProp3.meanC c w (P_pos j) := fun j =>
      SolRWPILimitProp3.meanC_nonneg c w (fun _ => hq_pos_prob j)
    have hCneg_nn : ∀ j : Fin r, 0 ≤ SolRWPILimitProp3.meanC c w (P_neg j) := fun j =>
      SolRWPILimitProp3.meanC_nonneg c w (fun _ => hq_neg_prob j)
    set M : ℝ := SolRWPILimitProp3.meanC c w P0 +
      ∑ j : Fin r, (SolRWPILimitProp3.meanC c w (P_pos j) + SolRWPILimitProp3.meanC c w (P_neg j))
    have hC0_le_M : SolRWPILimitProp3.meanC c w P0 ≤ M := by
      dsimp [M]
      linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => add_nonneg (hCpos_nn j) (hCneg_nn j)]
    have hCpos_le_M : ∀ j : Fin r, SolRWPILimitProp3.meanC c w (P_pos j) ≤ M := by
      intro j
      have hsingle : SolRWPILimitProp3.meanC c w (P_pos j) + SolRWPILimitProp3.meanC c w (P_neg j) ≤
          ∑ k : Fin r, (SolRWPILimitProp3.meanC c w (P_pos k) +
            SolRWPILimitProp3.meanC c w (P_neg k)) :=
        Finset.single_le_sum (fun k _ => add_nonneg (hCpos_nn k) (hCneg_nn k)) (Finset.mem_univ j)
      dsimp [M]; linarith [hC0_nn, hCneg_nn j]
    have hCneg_le_M : ∀ j : Fin r, SolRWPILimitProp3.meanC c w (P_neg j) ≤ M := by
      intro j
      have hsingle : SolRWPILimitProp3.meanC c w (P_pos j) + SolRWPILimitProp3.meanC c w (P_neg j) ≤
          ∑ k : Fin r, (SolRWPILimitProp3.meanC c w (P_pos k) +
            SolRWPILimitProp3.meanC c w (P_neg k)) :=
        Finset.single_le_sum (fun k _ => add_nonneg (hCpos_nn k) (hCneg_nn k)) (Finset.mem_univ j)
      dsimp [M]; linarith [hC0_nn, hCpos_nn j]
    set U : Set ((Fin r → ℝ) × ℝ) := {y : Fin r → ℝ | ∑ j : Fin r, |y j| < δ₁} ×ˢ Set.Ioi M
    have hU_open : IsOpen U :=
      (isOpen_lt (continuous_finsetSum Finset.univ fun j _ =>
        continuous_abs.comp (continuous_apply j)) continuous_const).prod isOpen_Ioi
    have h0M_mem_U : ((0 : Fin r → ℝ), M + 1) ∈ U := by
      refine ⟨?_, ?_⟩
      · simp [hδ₁_pos]
      · change M < M + 1; linarith
    have hU_sub_K : U ⊆ K := by
      rintro ⟨y, t⟩ ⟨hy_lt, ht_gt⟩
      change ∑ j : Fin r, |y j| < δ₁ at hy_lt
      change M < t at ht_gt
      set a_pos : Fin r → ℝ := fun j => max (y j / δ₁) 0
      set a_neg : Fin r → ℝ := fun j => max (-y j / δ₁) 0
      have hap_nn : ∀ j, 0 ≤ a_pos j := fun j => le_max_right _ _
      have han_nn : ∀ j, 0 ≤ a_neg j := fun j => le_max_right _ _
      have hap_add : ∀ j, a_pos j + a_neg j = |y j| / δ₁ := by
        intro j; dsimp [a_pos, a_neg]
        rcases le_or_gt 0 (y j) with hj | hj
        · have h1 : 0 ≤ y j / δ₁ := div_nonneg hj hδ₁_pos.le
          have h2 : -y j / δ₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hj) hδ₁_pos.le
          rw [max_eq_left h1, max_eq_right h2, add_zero, abs_of_nonneg hj]
        · have h1 : y j / δ₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hj.le hδ₁_pos.le
          have h2 : 0 ≤ -y j / δ₁ :=
            div_nonneg (neg_nonneg.mpr hj.le) hδ₁_pos.le
          rw [max_eq_right h1, max_eq_left h2, zero_add, abs_of_neg hj]
      have hap_sub : ∀ j, a_pos j - a_neg j = y j / δ₁ := by
        intro j; dsimp [a_pos, a_neg]
        rcases le_or_gt 0 (y j) with hj | hj
        · have h1 : 0 ≤ y j / δ₁ := div_nonneg hj hδ₁_pos.le
          have h2 : -y j / δ₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hj) hδ₁_pos.le
          rw [max_eq_left h1, max_eq_right h2, sub_zero]
        · have h1 : y j / δ₁ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hj.le hδ₁_pos.le
          have h2 : 0 ≤ -y j / δ₁ :=
            div_nonneg (neg_nonneg.mpr hj.le) hδ₁_pos.le
          rw [max_eq_right h1, max_eq_left h2]; ring
      set a0 : ℝ := 1 - ∑ j : Fin r, (a_pos j + a_neg j)
      have ha0_pos : 0 < a0 := by
        dsimp [a0]
        have hsum_eq : ∑ j : Fin r, (a_pos j + a_neg j) = (∑ j : Fin r, |y j|) / δ₁ := by
          simp_rw [hap_add, ← Finset.sum_div]
        rw [hsum_eq, sub_pos, div_lt_one hδ₁_pos]
        exact hy_lt
      have hwt_one : a0 + ∑ j : Fin r, a_pos j + ∑ j : Fin r, a_neg j = 1 := by
        dsimp [a0]; rw [Finset.sum_add_distrib]; ring
      set Py : Fin n → ((Fin m → ℝ) →₀ ℝ) :=
        a0 • P0 + ∑ j : Fin r, a_pos j • P_pos j + ∑ j : Fin r, a_neg j • P_neg j
      refine ⟨Py, ?_, ?_, ?_⟩
      · intro i
        refine ⟨fun u => ?_, ?_⟩
        · simp only [Py, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Finsupp.coe_add,
            Finsupp.coe_smul, Finsupp.finsetSum_apply, smul_eq_mul]
          refine add_nonneg (add_nonneg (mul_nonneg ha0_pos.le (hq0_prob.1 u)) ?_) ?_
          · exact Finset.sum_nonneg fun j _ => mul_nonneg (hap_nn j) ((hq_pos_prob j).1 u)
          · exact Finset.sum_nonneg fun j _ => mul_nonneg (han_nn j) ((hq_neg_prob j).1 u)
        · simp only [Py, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, map_add, map_smul,
            map_sum, smul_eq_mul, P0, P_pos, P_neg, hq0_prob.2,
            fun j => (hq_pos_prob j).2, fun j => (hq_neg_prob j).2, mul_one]
          exact hwt_one
      · simp only [Py, map_add, map_smul, map_sum, hP0_zero, smul_zero, zero_add,
          hP_pos_mean, hP_neg_mean]
        ext k
        let e : Fin r → (Fin r → ℝ) := fun j => Pi.single j (1 : ℝ)
        change (∑ j : Fin r, a_pos j • (δ₁ • e j)) k + (∑ j : Fin r, a_neg j • -(δ₁ • e j)) k = y k
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, mul_neg]
        rw [← Finset.sum_add_distrib]
        have hk : ∑ j : Fin r, (a_pos j * (δ₁ * e j k) + -(a_neg j * (δ₁ * e j k))) =
            ∑ j : Fin r, ((a_pos j - a_neg j) * δ₁) * e j k := by
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hk]
        simp_rw [hap_sub, div_mul_cancel₀ _ hδ₁_pos.ne']
        rw [Finset.sum_eq_single k]
        · simp [e]
        · intro j _ hjk; simp [e, Pi.single_eq_of_ne hjk.symm]
        · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
      · simp only [Py, map_add, map_smul, map_sum, smul_eq_mul]
        have hle_M : a0 * SolRWPILimitProp3.meanC c w P0 +
            ∑ j : Fin r, a_pos j * SolRWPILimitProp3.meanC c w (P_pos j) +
            ∑ j : Fin r, a_neg j * SolRWPILimitProp3.meanC c w (P_neg j) ≤
            (a0 + ∑ j : Fin r, a_pos j + ∑ j : Fin r, a_neg j) * M := by
          have h0 : a0 * SolRWPILimitProp3.meanC c w P0 ≤ a0 * M :=
            mul_le_mul_of_nonneg_left hC0_le_M ha0_pos.le
          have hp : ∑ j : Fin r, a_pos j * SolRWPILimitProp3.meanC c w (P_pos j) ≤
              (∑ j : Fin r, a_pos j) * M := by
            rw [Finset.sum_mul]
            exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (hCpos_le_M j) (hap_nn j)
          have hn' : ∑ j : Fin r, a_neg j * SolRWPILimitProp3.meanC c w (P_neg j) ≤
              (∑ j : Fin r, a_neg j) * M := by
            rw [Finset.sum_mul]
            exact Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (hCneg_le_M j) (han_nn j)
          linarith
        rw [hwt_one, one_mul] at hle_M
        exact hle_M.trans_lt ht_gt
    have h0M_int : ((0 : Fin r → ℝ), M + 1) ∈ interior K :=
      mem_interior.mpr ⟨U, hU_sub_K, hU_open, h0M_mem_U⟩
    obtain ⟨f, u_sep, hf_ne, hf_le, hf_ge⟩ :=
      geometric_hahn_banach_of_nonempty_interior hK_conv
        (convex_singleton ((0 : Fin r → ℝ), α_opt))
        (Set.disjoint_singleton_right.mpr fun h => hnot_mem (interior_subset h))
        ⟨((0 : Fin r → ℝ), M + 1), h0M_int⟩ (Set.singleton_nonempty _)
    set L : StrongDual ℝ ((Fin r → ℝ) × ℝ) := -f
    have hL_ne : L ≠ 0 := neg_ne_zero.mpr hf_ne
    have hL_sep : ∀ z ∈ K, L ((0 : Fin r → ℝ), α_opt) ≤ L z := by
      intro z hz
      have h1 : f z ≤ u_sep := hf_le z hz
      have h2 : u_sep ≤ f ((0 : Fin r → ℝ), α_opt) := hf_ge _ rfl
      simp only [L, neg_apply]
      linarith
    set μ_vec : Fin r → ℝ := fun j => L (Pi.single j 1, 0)
    set γ : ℝ := L (0, 1)
    have hL_eval : ∀ (y : Fin r → ℝ) (t : ℝ), L (y, t) = μ_vec ⬝ᵥ y + γ * t := by
      intro y t
      let e : Fin r → (Fin r → ℝ) := fun j => Pi.single j (1 : ℝ)
      have hy_eq : y = ∑ j : Fin r, y j • e j := by
        ext k
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single k]
        · simp [e]
        · intro j _ hjk; simp [e, Pi.single_eq_of_ne hjk.symm]
        · intro h_abs; exact absurd (Finset.mem_univ k) h_abs
      have hdecomp : (y, t) = ∑ j : Fin r, y j • (e j, (0 : ℝ)) +
          t • ((0 : Fin r → ℝ), (1 : ℝ)) := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum, ← hy_eq]
        · simp [Prod.snd_sum]
      rw [hdecomp, map_add, map_sum, map_smul, smul_eq_mul, mul_comm t γ]
      congr 1
      change ∑ j : Fin r, L (y j • (e j, 0)) = ∑ j : Fin r, μ_vec j * y j
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hα_le_C0 : α_opt ≤ SolRWPILimitProp3.meanC c w P0 := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hR_le_P0
      rwa [ENNReal.toReal_ofReal hC0_nn] at h1
    have hα_lt_M1 : α_opt < M + 1 := by linarith [hC0_le_M]
    have hγ_nonneg : 0 ≤ γ := by
      have h0M_K : ((0 : Fin r → ℝ), M + 1) ∈ K := hU_sub_K h0M_mem_U
      have hsep0 := hL_sep _ h0M_K
      rw [hL_eval, hL_eval, dotProduct_zero, zero_add, zero_add] at hsep0
      nlinarith
    have hγ_pos : 0 < γ := by
      rcases hγ_nonneg.eq_or_lt with hγ0 | hγ_pos
      · exfalso
        have hex_j : ∃ j₀ : Fin r, μ_vec j₀ ≠ 0 := by
          by_contra h_all
          push Not at h_all
          apply hL_ne
          refine ContinuousLinearMap.ext fun ⟨y, t⟩ => ?_
          simp [hL_eval, dotProduct, h_all, ← hγ0]
        obtain ⟨j₀, hj₀⟩ := hex_j
        set s : ℝ := if 0 ≤ μ_vec j₀ then -(δ₁ / 2) else δ₁ / 2
        have hs_abs : |s| = δ₁ / 2 := by
          dsimp [s]; split_ifs <;> simp [abs_of_pos (half_pos hδ₁_pos)]
        have hs_mul : μ_vec j₀ * s < 0 := by
          dsimp [s]
          split_ifs with hsign
          · have hpos : 0 < μ_vec j₀ := lt_of_le_of_ne hsign hj₀.symm
            nlinarith
          · have hneg : μ_vec j₀ < 0 := lt_of_not_ge hsign
            nlinarith
        set y_test : Fin r → ℝ := Pi.single j₀ s
        have hy_U : (y_test, M + 1) ∈ U := by
          refine ⟨?_, ?_⟩
          · change ∑ j : Fin r, |y_test j| < δ₁
            rw [Finset.sum_eq_single j₀]
            · simp only [y_test, Pi.single_eq_same, hs_abs]; linarith
            · intro j _ hjj₀; simp [y_test, Pi.single_eq_of_ne hjj₀]
            · intro h_abs; exact absurd (Finset.mem_univ j₀) h_abs
          · change M < M + 1; linarith
        have hsep_test := hL_sep _ (hU_sub_K hy_U)
        simp only [hL_eval, ← hγ0, dotProduct_zero, zero_mul, add_zero, y_test,
          dotProduct_single] at hsep_test
        linarith
      · exact hγ_pos
    set lam : Fin r → ℝ := -(γ⁻¹ • μ_vec)
    have htuple_bound : ∀ u_tup : Fin n → (Fin m → ℝ),
        (1 / (n : ℝ)) * ∑ i : Fin n, (lam ⬝ᵥ h (u_tup i) θ - (c (u_tup i) (w i)).toReal) ≤
          -α_opt := by
      intro u_tup
      set Pu : Fin n → ((Fin m → ℝ) →₀ ℝ) := fun i => Finsupp.single (u_tup i) 1
      have hPu_prob : ∀ i, SolRWPILimitProp3.IsProbFS (Pu i) := fun i =>
        SolRWPILimitProp3.isProbFS_single (u_tup i)
      have hPu_H : SolRWPILimitProp3.meanH (fun u => h u θ) Pu =
          (1 / (n : ℝ)) • ∑ i : Fin n, h (u_tup i) θ := by
        simp [SolRWPILimitProp3.meanH, Pu, SolRWPILimitProp3.evalFS_single]
      have hPu_C : SolRWPILimitProp3.meanC c w Pu =
          (1 / (n : ℝ)) * ∑ i : Fin n, (c (u_tup i) (w i)).toReal := by
        simp [SolRWPILimitProp3.meanC, Pu, SolRWPILimitProp3.evalFS_single]
      have hineq : γ * α_opt ≤ μ_vec ⬝ᵥ SolRWPILimitProp3.meanH (fun u => h u θ) Pu +
          γ * SolRWPILimitProp3.meanC c w Pu := by
        refine le_of_forall_pos_le_add fun ε hε => ?_
        have hmem : (SolRWPILimitProp3.meanH (fun u => h u θ) Pu,
            SolRWPILimitProp3.meanC c w Pu + ε / γ) ∈ K :=
          ⟨Pu, hPu_prob, rfl, by linarith [div_pos hε hγ_pos]⟩
        have hsep_u := hL_sep _ hmem
        rw [hL_eval, hL_eval, dotProduct_zero, zero_add, mul_add,
          mul_div_cancel₀ _ hγ_pos.ne'] at hsep_u
        linarith
      rw [hPu_H, hPu_C, dotProduct_smul, smul_eq_mul, dotProduct_sum] at hineq
      have hlam_dot : ∀ i : Fin n, μ_vec ⬝ᵥ h (u_tup i) θ = -γ * (lam ⬝ᵥ h (u_tup i) θ) := by
        intro i
        simp only [lam, neg_dotProduct, smul_dotProduct, smul_eq_mul]
        field_simp [hγ_pos.ne']
      simp_rw [hlam_dot, ← Finset.mul_sum] at hineq
      have hdiv : α_opt ≤ -(1 / (n : ℝ)) * ∑ i : Fin n, (lam ⬝ᵥ h (u_tup i) θ) +
          (1 / (n : ℝ)) * ∑ i : Fin n, (c (u_tup i) (w i)).toReal := by
        have h1 : γ * α_opt ≤ γ * (-(1 / (n : ℝ)) * ∑ i : Fin n, (lam ⬝ᵥ h (u_tup i) θ) +
            (1 / (n : ℝ)) * ∑ i : Fin n, (c (u_tup i) (w i)).toReal) := by linarith
        exact le_of_mul_le_mul_left h1 hγ_pos
      have hcomb : (1 / (n : ℝ)) * ∑ i : Fin n,
          (lam ⬝ᵥ h (u_tup i) θ - (c (u_tup i) (w i)).toReal) =
          (1 / (n : ℝ)) * ∑ i : Fin n, lam ⬝ᵥ h (u_tup i) θ -
          (1 / (n : ℝ)) * ∑ i : Fin n, (c (u_tup i) (w i)).toReal := by
        rw [Finset.sum_sub_distrib, mul_sub]
      linarith
    have hφ_ne_top : ∀ i₀ : Fin n, φ lam (w i₀) ≠ ⊤ := by
      classical
      intro i₀
      set B : ℝ := n * (-α_opt) -
        ∑ i ∈ Finset.univ.erase i₀, (lam ⬝ᵥ h (w i) θ - (c (w i) (w i)).toReal)
      have hle_B : φ lam (w i₀) ≤ ((B : ℝ) : EReal) := by
        refine iSup_le fun x => ?_
        rw [hφ_sub]
        refine EReal.coe_le_coe_iff.mpr ?_
        have hb := htuple_bound (Function.update w i₀ x)
        have hsum_upd : ∑ i : Fin n,
            (lam ⬝ᵥ h (Function.update w i₀ x i) θ -
              (c (Function.update w i₀ x i) (w i)).toReal) =
            (lam ⬝ᵥ h x θ - (c x (w i₀)).toReal) +
            ∑ i ∈ Finset.univ.erase i₀, (lam ⬝ᵥ h (w i) θ - (c (w i) (w i)).toReal) := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
          congr 1
          · simp
          · refine Finset.sum_congr rfl fun i hi => ?_
            have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
            simp [Function.update_of_ne hne]
        rw [hsum_upd] at hb
        have hb' : (lam ⬝ᵥ h x θ - (c x (w i₀)).toReal) +
            ∑ i ∈ Finset.univ.erase i₀, (lam ⬝ᵥ h (w i) θ - (c (w i) (w i)).toReal) ≤
            (n : ℝ) * (-α_opt) := by
          have := mul_le_mul_of_nonneg_left hb hn_pos.le
          rwa [← mul_assoc, mul_one_div_cancel hn_pos.ne', one_mul] at this
        dsimp [B]; linarith
      intro htop
      rw [htop] at hle_B
      exact EReal.coe_ne_top B (top_le_iff.mp hle_B)
    set s_val : Fin n → ℝ := fun i => (φ lam (w i)).toReal
    have hφ_eq_s : ∀ i : Fin n, φ lam (w i) = ((s_val i : ℝ) : EReal) := fun i =>
      (EReal.coe_toReal (hφ_ne_top i) (hφ_ne_bot lam (w i))).symm
    have hmean_s : (1 / (n : ℝ)) * ∑ i : Fin n, s_val i ≤ -α_opt := by
      refine le_of_forall_pos_le_add fun η hη => ?_
      have hex_u : ∀ i : Fin n, ∃ u_i : Fin m → ℝ,
          s_val i - η < lam ⬝ᵥ h u_i θ - (c u_i (w i)).toReal := by
        intro i
        have hlt : (((s_val i - η : ℝ) : EReal)) < φ lam (w i) := by
          rw [hφ_eq_s i]
          exact EReal.coe_lt_coe_iff.mpr (by linarith)
        obtain ⟨u_i, hu_i⟩ := lt_iSup_iff.mp hlt
        rw [hφ_sub] at hu_i
        exact ⟨u_i, EReal.coe_lt_coe_iff.mp hu_i⟩
      choose u_tup hu_tup using hex_u
      have hsum_lt : ∑ i : Fin n, (s_val i - η) ≤
          ∑ i : Fin n, (lam ⬝ᵥ h (u_tup i) θ - (c (u_tup i) (w i)).toReal) :=
        Finset.sum_le_sum fun i _ => (hu_tup i).le
      have havg := (mul_le_mul_of_nonneg_left hsum_lt (by positivity : 0 ≤ 1 / (n : ℝ))).trans
        (htuple_bound u_tup)
      have hsub_η : (1 / (n : ℝ)) * ∑ i : Fin n, (s_val i - η) =
          (1 / (n : ℝ)) * ∑ i : Fin n, s_val i - η := by
        rw [Finset.sum_sub_distrib, mul_sub, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← mul_assoc, one_div_mul_cancel hn_pos.ne', one_mul]
      linarith
    calc (R : EReal) = ((α_opt : ℝ) : EReal) := hR_ereal
      _ ≤ ((-((1 / (n : ℝ)) * ∑ i : Fin n, s_val i) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
      _ = -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam (w i)) := by
          simp_rw [hφ_eq_s]
          rw [SolRWPILimitProp3.finset_sum_coe_ereal, ← EReal.coe_mul, ← EReal.coe_neg]
      _ ≤ ⨆ lam' : Fin r → ℝ, -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam' (w i)) :=
          le_iSup (fun lam' : Fin r → ℝ =>
            -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam' (w i))) lam
  · -- Weak duality: RHS ≤ LHS
    refine iSup_le fun lam => ?_
    by_cases htop : ∃ i₀ : Fin n, φ lam (w i₀) = ⊤
    · obtain ⟨i₀, hi₀⟩ := htop
      have hsum_top : ∑ i : Fin n, φ lam (w i) = ⊤ := by
        classical
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀), hi₀]
        exact EReal.top_add_of_ne_bot
          (SolRWPILimitProp3.finset_sum_ne_bot _ _ fun i _ => hφ_ne_bot lam (w i))
      rw [hsum_top, EReal.coe_mul_top_of_pos (one_div_pos.mpr hn_pos), EReal.neg_top]
      exact bot_le
    · push Not at htop
      classical
      set W_fin : Finset (Fin m → ℝ) := Finset.univ.image w
      set g : (Fin m → ℝ) → ℝ := fun v => if v ∈ W_fin then (φ lam v).toReal else 0
      have hg_w : ∀ i : Fin n, g (w i) = (φ lam (w i)).toReal := fun i =>
        if_pos (Finset.mem_image_of_mem w (Finset.mem_univ i))
      have hφ_eq_g : ∀ i : Fin n, φ lam (w i) = ((g (w i) : ℝ) : EReal) := fun i => by
        rw [hg_w i]
        exact (EReal.coe_toReal (htop i) (hφ_ne_bot lam (w i))).symm
      have hlhs_eq : -(((1 / (n : ℝ) : ℝ) : EReal) * ∑ i : Fin n, φ lam (w i)) =
          ((-((1 / (n : ℝ)) * ∑ i : Fin n, g (w i)) : ℝ) : EReal) := by
        simp_rw [hφ_eq_g]
        rw [SolRWPILimitProp3.finset_sum_coe_ereal, ← EReal.coe_mul, ← EReal.coe_neg]
      rw [hlhs_eq]
      refine SolRWPILimitProp3.coe_real_le_ennreal_toEReal _ ?_
      refine le_iInf₂ fun P ⟨hP_prob, hP_int, hP_mean⟩ => ?_
      refine le_iInf₂ fun π ⟨hπ_prob, hπ_fst, hπ_snd⟩ => ?_
      by_cases hc_top : ∫⁻ z, c z.1 z.2 ∂π = ⊤
      · rw [hc_top]; exact le_top
      have hc_lt_top : ∫⁻ z, c z.1 z.2 ∂π < ⊤ := lt_top_iff_ne_top.mpr hc_top
      have hc_int : Integrable (fun z : (Fin m → ℝ) × (Fin m → ℝ) => (c z.1 z.2).toReal) π :=
        integrable_toReal_of_lintegral_ne_top hc_lsc.measurable.aemeasurable hc_top
      have hc_int_eq : ∫ z, (c z.1 z.2).toReal ∂π = (∫⁻ z, c z.1 z.2 ∂π).toReal :=
        integral_toReal hc_lsc.measurable.aemeasurable
          (Filter.Eventually.of_forall fun z => (hc_fin z.1 z.2).lt_top)
      have hW_meas : MeasurableSet (W_fin : Set (Fin m → ℝ)) := W_fin.measurableSet
      have hg_meas : Measurable g := by
        have hg_sum : g = fun v => ∑ y ∈ W_fin, Set.indicator {y} (fun _ => (φ lam y).toReal) v := by
          ext v
          dsimp [g]
          split_ifs with hv
          · rw [Finset.sum_eq_single v]
            · simp
            · intro y _ hyv; simp [Set.indicator_of_notMem, hyv.symm]
            · intro h_abs; exact absurd hv h_abs
          · rw [Finset.sum_eq_zero]
            intro y hy
            have hvy : v ≠ y := fun h_eq => hv (h_eq ▸ hy)
            simp [Set.indicator_of_notMem, hvy]
        rw [hg_sum]
        exact Finset.measurable_sum W_fin fun y _ =>
          measurable_const.indicator (measurableSet_singleton y)
      obtain ⟨Mg, hMg⟩ : ∃ Mg : ℝ, ∀ v : Fin m → ℝ, ‖g v‖ ≤ Mg := by
        refine ⟨∑ y ∈ W_fin, |(φ lam y).toReal|, fun v => ?_⟩
        rw [Real.norm_eq_abs]
        dsimp [g]
        split_ifs with hv
        · exact Finset.single_le_sum (f := fun y => |(φ lam y).toReal|)
            (fun y _ => abs_nonneg _) hv
        · rw [abs_zero]
          exact Finset.sum_nonneg fun y _ => abs_nonneg _
      have hg_π_int : Integrable (fun z : (Fin m → ℝ) × (Fin m → ℝ) => g z.2) π :=
        Integrable.of_bound (hg_meas.comp measurable_snd).aestronglyMeasurable Mg
          (Filter.Eventually.of_forall fun z => hMg z.2)
      have hg_int_eq : ∫ z, g z.2 ∂π = (1 / (n : ℝ)) * ∑ i : Fin n, g (w i) := by
        have hmap : ∫ z, g z.2 ∂π = ∫ v, g v ∂Pn := by
          rw [← hπ_snd]
          exact (integral_map measurable_snd.aemeasurable hg_meas.aestronglyMeasurable).symm
        rw [hmap]
        dsimp [Pn, empiricalDistribution]
        rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_eq_one_div,
          smul_eq_mul, integral_finsetSum_measure
            (fun i _ => integrable_dirac (by simp))]
        congr 1
        refine Finset.sum_congr rfl fun i _ => integral_dirac g (w i)
      set L_lam : (Fin r → ℝ) →L[ℝ] ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := fun x => lam ⬝ᵥ x
            map_add' := fun x y => dotProduct_add lam x y
            map_smul' := fun a x => by simp [dotProduct_smul] }
      have hlam_P_int : Integrable (fun u => lam ⬝ᵥ h u θ) P := L_lam.integrable_comp hP_int
      have hlam_π_int : Integrable (fun z : (Fin m → ℝ) × (Fin m → ℝ) => lam ⬝ᵥ h z.1 θ) π := by
        have h1 : Integrable (fun u => lam ⬝ᵥ h u θ) (π.map Prod.fst) := hπ_fst.symm ▸ hlam_P_int
        exact (integrable_map_measure (L_lam.continuous.measurable.comp hmeas).aestronglyMeasurable
          measurable_fst.aemeasurable).mp h1
      have hlam_int_eq : ∫ z, lam ⬝ᵥ h z.1 θ ∂π = 0 := by
        have hmap : ∫ z, lam ⬝ᵥ h z.1 θ ∂π = ∫ u, L_lam (h u θ) ∂P := by
          rw [← hπ_fst]
          exact (integral_map measurable_fst.aemeasurable
            (L_lam.continuous.measurable.comp hmeas).aestronglyMeasurable).symm
        rw [hmap, L_lam.integral_comp_comm hP_int, hP_mean, map_zero]
      have hae_W : ∀ᵐ z ∂π, z.2 ∈ W_fin := by
        rw [ae_iff]
        have hpre : {z : (Fin m → ℝ) × (Fin m → ℝ) | z.2 ∉ W_fin} = Prod.snd ⁻¹' (W_fin : Set _)ᶜ :=
          rfl
        rw [hpre, ← Measure.map_apply measurable_snd hW_meas.compl, hπ_snd]
        simp only [Pn, empiricalDistribution, Measure.smul_apply, Measure.coe_finsetSum,
          Finset.sum_apply, smul_eq_mul]
        have hsum0 : ∑ i : Fin n, Measure.dirac (w i) (W_fin : Set (Fin m → ℝ))ᶜ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [Measure.dirac_apply' _ hW_meas.compl]
          have hw_mem : w i ∈ (W_fin : Set (Fin m → ℝ)) :=
            Finset.mem_coe.mpr (Finset.mem_image_of_mem w (Finset.mem_univ i))
          simp [hw_mem]
        rw [hsum0, mul_zero]
      have hae_le : ∀ᵐ z ∂π, lam ⬝ᵥ h z.1 θ - g z.2 ≤ (c z.1 z.2).toReal := by
        filter_upwards [hae_W] with z hz
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
        rw [← hi]
        have hle_sup : (((lam ⬝ᵥ h z.1 θ : ℝ) : EReal) - (c z.1 (w i) : EReal)) ≤ φ lam (w i) :=
          le_iSup (fun u : Fin m → ℝ =>
            (((lam ⬝ᵥ h u θ : ℝ) : EReal) - (c u (w i) : EReal))) z.1
        rw [hφ_sub, hφ_eq_g i] at hle_sup
        have hreal := EReal.coe_le_coe_iff.mp hle_sup
        linarith
      have hint_ineq := integral_mono_ae (hlam_π_int.sub hg_π_int) hc_int hae_le
      change ∫ z, (lam ⬝ᵥ h z.1 θ - g z.2) ∂π ≤ ∫ z, (c z.1 z.2).toReal ∂π at hint_ineq
      rw [integral_sub hlam_π_int hg_π_int, hlam_int_eq, hg_int_eq, zero_sub, hc_int_eq] at hint_ineq
      rw [← ENNReal.ofReal_toReal hc_top]
      exact ENNReal.ofReal_le_ofReal hint_ineq
