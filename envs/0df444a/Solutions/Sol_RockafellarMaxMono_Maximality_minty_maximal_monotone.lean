-- Prove2me | solution 1 for RockafellarMaxMono.Maximality.minty_maximal_monotone
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:15:12.039893+00:00
-- url     : https://prove2.me/submissions/ab02bf76-1afe-4fe9-9aa9-ae633edda694

import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Maximality_MonotoneOperator

set_option autoImplicit false

/-- Ekeland's variational principle (weak form, with control of the value). -/
theorem rmm_ekeland {X : Type*} [MetricSpace X] [CompleteSpace X] (H : X → ℝ)
    (hH : LowerSemicontinuous H) (m : ℝ) (hm : ∀ x, m ≤ H x) (δ : ℝ) (hδ : 0 < δ) (x₁ : X) :
    ∃ x, H x ≤ H x₁ ∧ ∀ y, H x ≤ H y + δ * dist y x := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : X → Set X, ∀ z y, y ∈ S z ↔ H y + δ * dist y z ≤ H z :=
    ⟨fun z => {y | H y + δ * dist y z ≤ H z}, fun _ _ => Iff.rfl⟩
  have hself : ∀ z, z ∈ S z := by intro z; rw [hS]; simp
  have htrans : ∀ z y w, y ∈ S z → w ∈ S y → w ∈ S z := by
    intro z y w hy hw
    rw [hS] at hy hw ⊢
    have := dist_triangle w y z
    nlinarith
  have hclosed : ∀ z, IsClosed (S z) := by
    intro z
    have h1 : LowerSemicontinuous (fun y => H y + δ * dist y z) :=
      hH.add (Continuous.lowerSemicontinuous (by fun_prop))
    have h2 : S z = (fun y => H y + δ * dist y z) ⁻¹' Set.Iic (H z) := by
      ext y; rw [hS]; rfl
    rw [h2]
    exact h1.isClosed_preimage (H z)
  have hnext : ∀ z, ∃ y ∈ S z, ∀ w ∈ S y, δ * dist w y ≤ H z - H y := by
    intro z
    have hne : (H '' S z).Nonempty := ⟨H z, z, hself z, rfl⟩
    have hbdd : BddBelow (H '' S z) := ⟨m, by rintro _ ⟨y, -, rfl⟩; exact hm y⟩
    have hμ : sInf (H '' S z) ≤ H z := csInf_le hbdd ⟨z, hself z, rfl⟩
    obtain ⟨y, hy, hyμ⟩ : ∃ y ∈ S z, 2 * H y - H z ≤ sInf (H '' S z) := by
      rcases eq_or_lt_of_le hμ with h | h
      · exact ⟨z, hself z, by linarith⟩
      · obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne
          (show sInf (H '' S z) < (H z + sInf (H '' S z)) / 2 by linarith)
        exact ⟨y, hy, by linarith⟩
    refine ⟨y, hy, fun w hw => ?_⟩
    have hwz : w ∈ S z := htrans z y w hy hw
    have hw' : sInf (H '' S z) ≤ H w := csInf_le hbdd ⟨w, hwz, rfl⟩
    rw [hS] at hw
    linarith
  choose nxt hnxtS hnxt using hnext
  obtain ⟨z, hz0, hzs⟩ : ∃ z : ℕ → X, z 0 = x₁ ∧ ∀ n, z (n + 1) = nxt (z n) :=
    ⟨fun n => Nat.rec x₁ (fun _ p => nxt p) n, rfl, fun _ => rfl⟩
  have hstep : ∀ n, z (n + 1) ∈ S (z n) := fun n => by rw [hzs]; exact hnxtS _
  have hnest : ∀ n k, n ≤ k → S (z k) ⊆ S (z n) := by
    intro n k hnk
    induction k, hnk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hnk ih => exact fun w hw => ih (htrans _ _ _ (hstep k) hw)
  have hmem : ∀ n k, n ≤ k → z k ∈ S (z n) := fun n k hnk => hnest n k hnk (hself _)
  have hanti : Antitone (fun n => H (z n)) := by
    refine antitone_nat_of_succ_le fun n => ?_
    have h1 := hstep n
    rw [hS] at h1
    have := dist_nonneg (x := z (n + 1)) (y := z n)
    nlinarith
  have hbddz : BddBelow (Set.range fun n => H (z n)) := ⟨m, by rintro _ ⟨n, rfl⟩; exact hm _⟩
  have hlimH := tendsto_atTop_ciInf hanti hbddz
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ⨅ n, H (z n) := ⟨_, rfl⟩
  rw [← hL] at hlimH
  have hLle : ∀ n, L ≤ H (z n) := fun n => hL ▸ ciInf_le hbddz n
  have hgap : ∀ n, ∀ w ∈ S (z (n + 1)), δ * dist w (z (n + 1)) ≤ H (z n) - L := by
    intro n w hw
    have h1 := hnxt (z n) w (by rw [← hzs]; exact hw)
    rw [← hzs] at h1
    linarith [hLle (n + 1)]
  have he : Filter.Tendsto (fun n => H (z n) - L) Filter.atTop (nhds 0) := by
    simpa using hlimH.sub_const L
  have hcauchy : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev := he.eventually (gt_mem_nhds (show (0:ℝ) < δ * ε by positivity))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N + 1, fun n hn => ?_⟩
    have h1 := hgap N (z n) (hmem (N + 1) n hn)
    have h2 := hN N le_rfl
    have h3 : δ * dist (z n) (z (N + 1)) < δ * ε := by linarith
    exact lt_of_mul_lt_mul_left h3 hδ.le
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxS : ∀ n, x ∈ S (z n) := fun n =>
    (hclosed _).mem_of_tendsto hx (Filter.eventually_atTop.2 ⟨n, fun k hk => hmem n k hk⟩)
  refine ⟨x, ?_, fun y => ?_⟩
  · have h1 := hxS 0
    rw [hS, hz0] at h1
    have := dist_nonneg (x := x) (y := x₁)
    nlinarith
  · by_contra hlt
    push Not at hlt
    have hyx : y ∈ S x := by rw [hS]; exact hlt.le
    have hbound : ∀ n, δ * dist y x ≤ 2 * (H (z n) - L) := by
      intro n
      have h1 := hgap n y (htrans _ _ _ (hxS (n + 1)) hyx)
      have h2 := hgap n x (hxS (n + 1))
      have h3 := dist_triangle y (z (n + 1)) x
      rw [dist_comm (z (n + 1)) x] at h3
      nlinarith
    have h0 : δ * dist y x ≤ 0 := by
      have h4 := he.const_mul 2
      simp only [mul_zero] at h4
      exact ge_of_tendsto' h4 hbound
    have hd : dist y x = 0 :=
      le_antisymm (by nlinarith [dist_nonneg (x := y) (y := x)]) dist_nonneg
    rw [dist_eq_zero] at hd
    subst hd
    simp at hlt

open RockafellarMaxMono in
theorem rmm_le_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (y : E) (r : ℝ) :
    f y ≤ (r : EReal) ↔ f y ≠ ⊤ ∧ (f y).toReal ≤ r := by
  constructor
  · intro h
    have hne : f y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) h
    refine ⟨hne, ?_⟩
    rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne (hf.1 y)]
    exact h
  · rintro ⟨hne, h⟩
    rw [← EReal.coe_toReal hne (hf.1 y)]
    exact EReal.coe_le_coe_iff.2 h

open RockafellarMaxMono in
theorem rmm_conv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x y : E) (r s a b : ℝ) (hx : f x ≤ (r : EReal))
    (hy : f y ≤ (s : EReal)) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * r + b * s : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    have ha1 : a = 1 := by linarith
    subst ha1
    simpa using hx
  rcases eq_or_lt_of_le (show b ≤ 1 by linarith) with hb1 | hb1
  · subst hb1
    have ha0 : a = 0 := by linarith
    subst ha0
    simpa using hy
  have ha' : a = 1 - b := by linarith
  subst ha'
  obtain ⟨hx1, hx2⟩ := (rmm_le_coe f hf x r).1 hx
  obtain ⟨hy1, hy2⟩ := (rmm_le_coe f hf y s).1 hy
  obtain ⟨p, hp, hpr⟩ : ∃ p : ℝ, f x = p ∧ p ≤ r :=
    ⟨_, (EReal.coe_toReal hx1 (hf.1 x)).symm, hx2⟩
  obtain ⟨q, hq, hqs⟩ : ∃ q : ℝ, f y = q ∧ q ≤ s :=
    ⟨_, (EReal.coe_toReal hy1 (hf.1 y)).symm, hy2⟩
  have hc := hf.2.2 x y b hbpos hb1
  rw [hp, hq, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hc
  refine hc.trans (EReal.coe_le_coe_iff.2 ?_)
  have h1 : 0 ≤ 1 - b := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hpr h1, mul_le_mul_of_nonneg_left hqs hbpos.le]

open RockafellarMaxMono in
theorem rmm_epi_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (ψ : StrongDual ℝ E) (κ : ℝ) :
    Convex ℝ {p : E × ℝ | f p.1 ≤ ((p.2 + ψ p.1 + κ : ℝ) : EReal)} := by
  intro p hp q hq a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hp hq ⊢
  have h := rmm_conv_le f hf p.1 q.1 _ _ a b hp hq ha hb hab
  have heq : (a • p + b • q).2 + ψ (a • p + b • q).1 + κ
      = a * (p.2 + ψ p.1 + κ) + b * (q.2 + ψ q.1 + κ) := by
    simp only [Prod.snd_add, Prod.fst_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_add,
      map_smul]
    linear_combination (-κ) * hab
  rw [heq]
  simpa only [Prod.fst_add, Prod.smul_fst] using h

theorem rmm_epi_closed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
  have h := hlsc.isClosed_epigraph
  exact h.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

open RockafellarMaxMono in
theorem rmm_minorant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∃ (a : StrongDual ℝ E) (b : ℝ), ∀ x, f x ≠ ⊤ → a x + b ≤ (f x).toReal := by
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hconv : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    have := rmm_epi_convex f hf 0 0
    simpa using this
  have hnot : ((x1, (f x1).toReal - 1) : E × ℝ) ∉ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro h
    simp only [Set.mem_ofPred_eq] at h
    rw [rmm_le_coe f hf] at h
    linarith [h.2]
  obtain ⟨ℓ, u, hℓ0, hℓ⟩ := geometric_hahn_banach_point_closed hconv (rmm_epi_closed f hlsc) hnot
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hmem : ∀ y, f y ≠ ⊤ →
      ((y, (f y).toReal) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro y hy
    simp only [Set.mem_ofPred_eq]
    rw [EReal.coe_toReal hy (hf.1 y)]
  have h1 := hℓ _ (hmem x1 hx1)
  rw [hdec] at h1 hℓ0
  have hc : 0 < ℓ (0, 1) := by nlinarith
  refine ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), u / ℓ (0, 1), fun x hx => ?_⟩
  have h2 := hℓ _ (hmem x hx)
  rw [hdec] at h2
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul]
  have e : -(ℓ (0, 1))⁻¹ * ℓ (x, 0) + u / ℓ (0, 1) = (u - ℓ (x, 0)) / ℓ (0, 1) := by
    field_simp
    ring
  rw [e, div_le_iff₀ hc]
  linarith

open RockafellarMaxMono in
theorem rmm_subdiff_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hf : Shared.ProperConvex f) (x : E) (x' : StrongDual ℝ E) (h : x' ∈ Shared.subdiff f x) :
    f x ≠ ⊤ := by
  intro hx
  obtain ⟨z, hz⟩ := hf.2.1
  have h1 := (show ∀ y, f x + ((x' (y - x) : ℝ) : EReal) ≤ f y from h) z
  rw [hx, EReal.top_add_coe] at h1
  exact hz (top_le_iff.1 h1)

open RockafellarMaxMono in
theorem rmm_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0))
    (η : ℝ) (hη : 0 < η) :
    f x0 ≠ ⊤ ∧ ∀ y, f y ≠ ⊤ →
      (f x0).toReal + x0' (y - x0) - η * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ (f y).toReal := by
  classical
  obtain ⟨a, b, hab⟩ := rmm_minorant f hf hlsc
  obtain ⟨x1, hx1⟩ := hf.2.1
  have hfF : ∀ x, f x ≠ ⊤ → f x = (((f x).toReal : ℝ) : EReal) :=
    fun x hx => (EReal.coe_toReal hx (hf.1 x)).symm
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / 2 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨k, hk⟩ : ∃ k : E → ℝ, ∀ x, k x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hkcont : Continuous k := by
    have : k = fun x => η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := funext hk
    rw [this]; fun_prop
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, ∀ x, g x = (f x).toReal - x0' (x - x0) := ⟨_, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = g x1 + k x1 + 1 := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : E → ℝ, ∀ x, H x = if f x = ⊤ then M else min (g x + k x) M :=
    ⟨_, fun _ => rfl⟩
  -- lower semicontinuity of the truncated function
  have hHlsc : LowerSemicontinuous H := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : M ≤ c
    · have : H ⁻¹' Set.Iic c = Set.univ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
        rw [hH]
        split_ifs
        · exact hc
        · exact (min_le_right _ _).trans hc
      rw [this]; exact isClosed_univ
    · push Not at hc
      have : H ⁻¹' Set.Iic c = (fun x => ((x, c + x0' (x - x0) - k x) : E × ℝ)) ⁻¹'
          {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        rw [rmm_le_coe f hf, hH]
        split_ifs with hx
        · simp only [hx, ne_eq, not_true_eq_false, false_and, iff_false, not_le]
          exact hc
        · rw [min_le_iff, hg]
          constructor
          · rintro (h | h)
            · exact ⟨hx, by linarith⟩
            · linarith
          · rintro ⟨-, h⟩
            left; linarith
      rw [this]
      exact (rmm_epi_closed f hlsc).preimage (continuous_id.prodMk
        ((continuous_const.add (x0'.continuous.comp (continuous_id.sub continuous_const))).sub
          hkcont))
  -- lower bound
  have hHbdd : ∀ x, min (a x0 + b - ‖a - x0'‖ ^ 2 / (4 * η)) M ≤ H x := by
    intro x
    rw [hH x]
    split_ifs with hx
    · exact min_le_right _ _
    · refine min_le_min_right _ ?_
      have h1 := hab x hx
      rw [hg, hk]
      have h2 := (a - x0').le_opNorm (x - x0)
      have h3 := neg_abs_le ((a - x0') (x - x0))
      rw [← Real.norm_eq_abs] at h3
      have h4 : (a - x0') (x - x0) = a x - a x0 - x0' (x - x0) := by
        rw [ContinuousLinearMap.sub_apply, map_sub]
      have hβ : ‖a - x0'‖ ^ 2 / (4 * η) * (4 * η) = ‖a - x0'‖ ^ 2 := by
        field_simp
      have ht := norm_nonneg (x - x0)
      have hC := norm_nonneg (a - x0')
      nlinarith [sq_nonneg (2 * η * ‖x - x0‖ - ‖a - x0'‖), mul_nonneg hη.le ht]
  -- Ekeland point
  obtain ⟨x, hxH, hxE⟩ := rmm_ekeland H hHlsc _ hHbdd δ hδpos x1
  have hH1 : H x1 = g x1 + k x1 := by
    rw [hH, if_neg hx1, min_eq_left (by rw [hM]; linarith)]
  rw [hH1] at hxH
  have hxfin : f x ≠ ⊤ := by
    intro hx
    rw [hH, if_pos hx] at hxH
    rw [hM] at hxH
    linarith
  have hHx : H x = g x + k x := by
    have hxH' := hxH
    rw [hH, if_neg hxfin] at hxH' ⊢
    rcases min_choice (g x + k x) M with h | h
    · exact h
    · rw [h] at hxH'; rw [hM] at hxH'; linarith
  have hEk : ∀ y, f y ≠ ⊤ → g x + k x ≤ g y + k y + δ * ‖y - x‖ := by
    intro y hy
    have h1 := hxE y
    rw [hHx, dist_eq_norm] at h1
    have h2 : H y ≤ g y + k y := by rw [hH, if_neg hy]; exact min_le_left _ _
    linarith
  -- the perturbation
  obtain ⟨K, hK⟩ : ∃ K : E → ℝ, ∀ y, K y = k y + δ * ‖y - x‖ := ⟨_, fun _ => rfl⟩
  have hKcont : Continuous K := by
    have : K = fun y => k y + δ * ‖y - x‖ := funext hK
    rw [this]; fun_prop
  have hKx : K x = k x := by rw [hK, sub_self, norm_zero, mul_zero, add_zero]
  have hnc : ∀ (u v : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → ‖s • u + t • v‖ ≤ s * ‖u‖ + t * ‖v‖ := by
    intro u v s t hs ht
    calc ‖s • u + t • v‖ ≤ ‖s • u‖ + ‖t • v‖ := norm_add_le _ _
      _ = s * ‖u‖ + t * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have hKconv : ∀ (y z : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → s + t = 1 →
      K (s • y + t • z) ≤ s * K y + t * K z := by
    intro y z s t hs ht hst
    have e1 : s • y + t • z - x0 = s • (y - x0) + t • (z - x0) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    have e2 : s • y + t • z - x = s • (y - x) + t • (z - x) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hst, one_smul]
    rw [hK, hK, hK, hk, hk, hk, e1, e2]
    have n1 := hnc (y - x0) (z - x0) s t hs ht
    have n2 := hnc (y - x) (z - x) s t hs ht
    have n0 := norm_nonneg (s • (y - x0) + t • (z - x0))
    have hsq : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
      have h1 : ‖s • (y - x0) + t • (z - x0)‖ ^ 2 ≤ (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 :=
        pow_le_pow_left₀ n0 n1 2
      have h2 : (s * ‖y - x0‖ + t * ‖z - x0‖) ^ 2 ≤ s * ‖y - x0‖ ^ 2 + t * ‖z - x0‖ ^ 2 := by
        have ht' : t = 1 - s := by linarith
        subst ht'
        nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (‖y - x0‖ - ‖z - x0‖))]
      linarith
    have m1 := mul_le_mul_of_nonneg_left n1 hη.le
    have m2 := mul_le_mul_of_nonneg_left hsq hη.le
    have m3 := mul_le_mul_of_nonneg_left n2 hδpos.le
    nlinarith
  -- the two convex sets
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = g x - x0' x0 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Set (E × ℝ), A = {p : E × ℝ | f p.1 ≤ ((p.2 + x0' p.1 + κ : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set (E × ℝ), B = {p : E × ℝ | p.2 < -(K p.1 - K x)} := ⟨_, rfl⟩
  have hAconv : Convex ℝ A := hA ▸ rmm_epi_convex f hf x0' κ
  have hBopen : IsOpen B := by
    rw [hB]
    exact isOpen_lt continuous_snd (((hKcont.comp continuous_fst).sub continuous_const).neg)
  have hBconv : Convex ℝ B := by
    rw [hB]
    intro p hp q hq s t hs ht hst
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    have hc := hKconv p.1 q.1 s t hs ht hst
    have hd1 : 0 < -(K p.1 - K x) - p.2 := by linarith
    have hd2 : 0 < -(K q.1 - K x) - q.2 := by linarith
    have hkey : 0 < s * (-(K p.1 - K x) - p.2) + t * (-(K q.1 - K x) - q.2) := by
      rcases eq_or_lt_of_le hs with hs0 | hspos
      · subst hs0
        have ht1 : t = 1 := by linarith
        subst ht1
        linarith
      · have := mul_pos hspos hd1
        have := mul_nonneg ht hd2.le
        linarith
    have hKx' : K x = s * K x + t * K x := by rw [← add_mul, hst, one_mul]
    nlinarith
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    intro p hpB hpA
    rw [hB] at hpB
    rw [hA] at hpA
    simp only [Set.mem_ofPred_eq] at hpB hpA
    rw [rmm_le_coe f hf] at hpA
    obtain ⟨hp1, hp2⟩ := hpA
    have h1 := hEk p.1 hp1
    rw [hK p.1, hKx] at hpB
    rw [hg p.1, hg x] at h1
    rw [hκ, hg x] at hp2
    simp only [map_sub] at h1 hp2
    linarith
  obtain ⟨ℓ, u, hℓB, hℓA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  have hdec : ∀ (y : E) (r : ℝ), ℓ (y, r) = ℓ (y, 0) + r * ℓ (0, 1) := by
    intro y r
    have : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hlin : ∀ y z : E, ℓ (y - z, 0) = ℓ (y, 0) - ℓ (z, 0) := by
    intro y z
    have : ((y - z, (0 : ℝ)) : E × ℝ) = (y, 0) - (z, 0) := by ext <;> simp
    rw [this, map_sub]
  have hxA : ((x, 0) : E × ℝ) ∈ A := by
    rw [hA]
    simp only [Set.mem_ofPred_eq]
    rw [rmm_le_coe f hf]
    refine ⟨hxfin, ?_⟩
    rw [hκ, hg, map_sub]
    linarith
  have hxB : ((x, -1) : E × ℝ) ∈ B := by
    rw [hB]
    simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
    norm_num
  have hu1 := hℓA _ hxA
  have hu2 := hℓB _ hxB
  rw [hdec] at hu2
  have hc : 0 < ℓ (0, 1) := by linarith
  have hu : u = ℓ (x, 0) := by
    by_contra hne
    have hlt : u < ℓ (x, 0) := lt_of_le_of_ne hu1 hne
    have hB' : ((x, (u - ℓ (x, 0)) / ℓ (0, 1)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq, sub_self, neg_zero]
      exact div_neg_of_neg_of_pos (by linarith) hc
    have h1 := hℓB _ hB'
    rw [hdec, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  obtain ⟨ψ, hψ⟩ : ∃ ψ : StrongDual ℝ E, ∀ v, ψ v = -(ℓ (v, 0)) / ℓ (0, 1) :=
    ⟨-(ℓ (0, 1))⁻¹ • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ), fun v => by
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply, smul_eq_mul]
      field_simp⟩
  have hS1 : ∀ y, f y ≠ ⊤ → ψ (y - x) ≤ g y - g x := by
    intro y hy
    have hyA : ((y, g y - g x) : E × ℝ) ∈ A := by
      rw [hA]
      simp only [Set.mem_ofPred_eq]
      rw [rmm_le_coe f hf]
      refine ⟨hy, ?_⟩
      rw [hκ, hg y, hg x, map_sub, map_sub]
      linarith
    have h1 := hℓA _ hyA
    rw [hdec] at h1
    rw [hψ, hlin, div_le_iff₀ hc]
    linarith
  have hS2 : ∀ y, -ψ (y - x) ≤ K y - K x := by
    intro y
    by_contra hlt
    push Not at hlt
    have hyB : ((y, ψ (y - x)) : E × ℝ) ∈ B := by
      rw [hB]
      simp only [Set.mem_ofPred_eq]
      linarith
    have h1 := hℓB _ hyB
    rw [hdec, hψ, hlin, div_mul_cancel₀ _ hc.ne'] at h1
    linarith
  have hsub : ψ + x0' ∈ Shared.subdiff f x := by
    show ∀ y, f x + (((ψ + x0') (y - x) : ℝ) : EReal) ≤ f y
    intro y
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · rw [hfF x hxfin, hfF y hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h1 := hS1 y hy
      rw [hg, hg] at h1
      simp only [ContinuousLinearMap.add_apply, map_sub] at h1 ⊢
      linarith
  have hmono := hrel x _ hsub
  simp only [add_sub_cancel_right] at hmono
  have hx0 : x = x0 := by
    have h := hS2 x0
    have e1 : K x0 = δ * ‖x - x0‖ := by
      rw [hK, hk, sub_self, norm_zero, norm_sub_rev]; ring
    have e2 : K x = η * ‖x - x0‖ + η * ‖x - x0‖ ^ 2 := by rw [hKx, hk]
    rw [e1, e2, map_sub] at h
    rw [map_sub] at hmono
    have ht := norm_nonneg (x - x0)
    have h0 : ‖x - x0‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖x - x0‖ := lt_of_le_of_ne ht (Ne.symm hne)
      have := mul_pos hη hpos
      nlinarith [sq_nonneg ‖x - x0‖]
    rwa [norm_eq_zero, sub_eq_zero] at h0
  refine ⟨hx0 ▸ hxfin, fun y hy => ?_⟩
  have h1 := hS1 y hy
  have h2 := hS2 y
  rw [hK y, hKx, hk, hk] at h2
  rw [hx0] at h1 h2
  rw [hg, hg, sub_self, map_zero, sub_zero] at h1
  rw [sub_self, norm_zero] at h2
  have hw := norm_nonneg (y - x0)
  nlinarith [mul_nonneg hη.le hw]

open RockafellarMaxMono in
theorem rmm_key {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x0 : E) (x0' : StrongDual ℝ E)
    (hrel : ∀ x, ∀ u ∈ Shared.subdiff f x, 0 ≤ (u - x0') (x - x0)) :
    x0' ∈ Shared.subdiff f x0 := by
  have hfin := (rmm_step f hf hlsc x0 x0' hrel 1 one_pos).1
  show ∀ y, f x0 + ((x0' (y - x0) : ℝ) : EReal) ≤ f y
  intro y
  by_cases hy : f y = ⊤
  · rw [hy]; exact le_top
  rw [← EReal.coe_toReal hfin (hf.1 x0), ← EReal.coe_toReal hy (hf.1 y), ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hw : 0 ≤ ‖y - x0‖ := norm_nonneg _
  have hden : 0 < 2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1 := by positivity
  have h := (rmm_step f hf hlsc x0 x0' hrel (ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1))
    (div_pos hε hden)).2 y hy
  have h3 : ε / (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2 + 1) * (2 * ‖y - x0‖ + ‖y - x0‖ ^ 2) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  linarith

open RockafellarMaxMono RockafellarMaxMono.Maximality in
theorem rock_subdiff_maximal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    IsMaximalMonotone (Shared.subdiff f) := by
  have hmono : IsMonotoneOp (Shared.subdiff f) := by
    intro x₀ x₁ x₀' x₁' h0 h1
    have hfin0 := rmm_subdiff_fin f hf x₀ x₀' h0
    have hfin1 := rmm_subdiff_fin f hf x₁ x₁' h1
    have a0 := (show ∀ y, f x₀ + ((x₀' (y - x₀) : ℝ) : EReal) ≤ f y from h0) x₁
    have a1 := (show ∀ y, f x₁ + ((x₁' (y - x₁) : ℝ) : EReal) ≤ f y from h1) x₀
    rw [← EReal.coe_toReal hfin0 (hf.1 x₀), ← EReal.coe_toReal hfin1 (hf.1 x₁),
      ← EReal.coe_add, EReal.coe_le_coe_iff] at a0 a1
    simp only [ContinuousLinearMap.sub_apply, map_sub] at a0 a1 ⊢
    linarith
  refine ⟨hmono, fun T' hT' hsub x => ?_⟩
  ext x'
  constructor
  · intro hx'
    exact rmm_key f hf hlsc x x' fun z u hu => hT' z x u x' (hsub z hu) hx'
  · intro hx'
    exact hsub x hx'

open RockafellarMaxMono RockafellarMaxMono.Maximality
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h) :
    IsMaximalMonotone (Shared.subdiff (fun x => ((h x : ℝ) : EReal))) := by
  apply rock_subdiff_maximal
  · refine ⟨fun _ => EReal.coe_ne_bot _,⟨0,EReal.coe_ne_top _⟩,fun x y t ht ht1 => ?_⟩
    rw [← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,EReal.coe_le_coe_iff]
    simpa only [smul_eq_mul] using hconv.2 (Set.mem_univ x) (Set.mem_univ y)
      (show 0 ≤ 1-t by linarith) ht.le (by ring : 1-t+t=1)
  · exact (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
