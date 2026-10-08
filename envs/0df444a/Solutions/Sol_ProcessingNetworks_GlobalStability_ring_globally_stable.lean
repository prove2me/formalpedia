-- Prove2me | solution 1 for ProcessingNetworks.GlobalStability.ring_globally_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:35:26.963378+00:00
-- url     : https://prove2.me/submissions/008da0ad-b0d7-4505-a9d3-97c8ed6e8a84

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_GlobalStability_UnidirectionalRing
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel

open MeasureTheory Filter Topology Set

namespace ProcessingNetworks.GlobalStability

noncomputable def rgDini (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

theorem rgd_dini_of_hasDerivAt (f : ℝ → ℝ) (d t : ℝ) (h : HasDerivAt f d t) :
    rgDini f t = (d : EReal) := by
  have h1 := h.tendsto_slope_zero_right
  have h2 : Tendsto (fun s : ℝ => (((f (t + s) - f t) / s : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (d : EReal)) :=
    (continuous_coe_real_ereal.tendsto d).comp (h1.congr fun s => by
      simp [smul_eq_mul, div_eq_inv_mul])
  exact h2.limsup_eq

theorem rgd_freq (f : ℝ → ℝ) (x M : ℝ) (hD : rgDini f x ≤ (M : EReal)) (r : ℝ)
    (hr : M < r) : ∃ᶠ z in 𝓝[>] x, slope f x z < r := by
  have hlt : rgDini f x < (r : EReal) := lt_of_le_of_lt hD (EReal.coe_lt_coe_iff.mpr hr)
  have e : ∀ᶠ h in 𝓝[>] (0 : ℝ), (((f (x + h) - f x) / h : ℝ) : EReal) < (r : EReal) :=
    eventually_lt_of_limsup_lt hlt
  have ht : Tendsto (fun z : ℝ => z - x) (𝓝[>] x) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun z : ℝ => z - x) (𝓝 x) (𝓝 (x - x)) :=
        ((continuous_id.sub continuous_const).tendsto x)
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_pos.mpr (show x < z from hz)
  refine (ht.eventually e).mono (fun z hz => ?_) |>.frequently
  rw [slope_def_field]
  simp only [add_sub_cancel] at hz
  exact EReal.coe_lt_coe_iff.mp hz

theorem rgd_upper (f : ℝ → ℝ) (a b M : ℝ) (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal)) :
    ∀ x ∈ Icc a b, f x ≤ f a + M * (x - a) := by
  intro x hx
  refine le_of_forall_pos_le_add fun η hη => ?_
  set δ := η / (x - a + 1) with hδ
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hδpos : 0 < δ := by positivity
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (f' := fun _ => M) hc
    (fun t ht r hr => rgd_freq f t M (hD t ht) r hr)
    (B := fun t => f a + (M + δ) * (t - a)) (B' := fun _ => M + δ) (by simp)
    (by fun_prop)
    (fun t _ => (((hasDerivAt_id t).sub_const a).const_mul (M + δ)).const_add (f a)
      |>.hasDerivWithinAt |>.congr_deriv (by simp))
    (fun t _ _ => by linarith) hx
  have : δ * (x - a) ≤ η := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

theorem rgd_mono (f : ℝ → ℝ) (a b M : ℝ) (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal)) :
    MonotoneOn (fun t => M * t - f t) (Icc a b) := by
  intro x hx y hy hxy
  have := rgd_upper f x y M (hc.mono (Icc_subset_Icc hx.1 hy.2))
    (fun t ht => hD t ⟨hx.1.trans ht.1, lt_of_lt_of_le ht.2 hy.2⟩) y ⟨hxy, le_rfl⟩
  simp only
  linarith

theorem rgd_decrease (f : ℝ → ℝ) (a b M ε : ℝ) (ha : 0 < a) (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hD : ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal))
    (hpos : ∀ t ∈ Ioo a b, 0 < f t)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → rgDini f t ≤ ((-ε : ℝ) : EReal)) :
    f b ≤ f a - ε * (b - a) := by
  set h : ℝ → ℝ := fun t => M * t - f t with hh
  have hmono : MonotoneOn h (Icc a b) := rgd_mono f a b M hc hD
  have hmono' : MonotoneOn h (uIcc a b) := by rwa [uIcc_of_le hab.le]
  have hint := hmono'.intervalIntegral_deriv_mem_uIcc
  have hhab : 0 ≤ h b - h a := sub_nonneg.mpr (hmono ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le)
  rw [uIcc_of_le hhab] at hint
  have hii := hmono'.intervalIntegrable_deriv
  have hfin : ({a, b} : Set ℝ).Finite := by simp
  have hae : ∀ᵐ x, x ∈ ({a, b} : Set ℝ)ᶜ := compl_mem_ae_iff.mpr (hfin.measure_zero _)
  have hlow : (fun _ => M + ε) ≤ᵐ[volume.restrict (Icc a b)] deriv h := by
    show ∀ᵐ x ∂(volume.restrict (Icc a b)), M + ε ≤ deriv h x
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hmono.ae_differentiableWithinAt_of_mem, hdrift, hae] with x hd hdr hne hx
    have hxa : x ≠ a := fun e => hne (by simp [e])
    have hxb : x ≠ b := fun e => hne (by simp [e])
    have hxI : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
    have hdiff : DifferentiableAt ℝ h x := (hd hx).differentiableAt (Icc_mem_nhds hxI.1 hxI.2)
    have hfeq : f = fun t => M * t - h t := by funext t; simp [hh]
    have hfd : HasDerivAt f (M - deriv h x) x := by
      rw [hfeq]
      have := ((hasDerivAt_id x).const_mul M).sub hdiff.hasDerivAt
      simp only [mul_one, id] at this
      exact this
    have := hdr (ha.le.trans hx.1) (hpos x hxI)
    rw [rgd_dini_of_hasDerivAt f _ x hfd, EReal.coe_le_coe_iff] at this
    show M + ε ≤ deriv h x
    linarith
  have hmono_int := intervalIntegral.integral_mono_ae_restrict hab.le
    intervalIntegrable_const hii hlow
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono_int
  have := hint.2
  simp only [hh] at this
  nlinarith

theorem rgd_induct (f : ℝ → ℝ) (hcont : ContinuousOn f (Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Ico a b, rgDini f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → rgDini f t ≤ ((-ε : ℝ) : EReal))
    (a δ C : ℝ) (ha : 0 < a) (hδ : 0 < δ) (h0 : f a ≤ max δ (C - ε * a)) :
    ∀ x, a ≤ x → f x ≤ max δ (C - ε * x) := by
  intro x hx
  set g : ℝ → ℝ := fun y => max δ (C - ε * y) with hg
  have hgc : Continuous g := by fun_prop
  have hfc : ∀ y, 0 < y → ContinuousAt f y := fun y hy =>
    hcont.continuousAt (isOpen_Ioi.mem_nhds hy)
  have hsub : Icc a x ⊆ {y | f y ≤ g y} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ h0 ?_
    · have hcI : ContinuousOn (fun y => g y - f y) (Icc a x) :=
        hgc.continuousOn.sub (hcont.mono fun y hy => lt_of_lt_of_le ha hy.1)
      have := hcI.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
      convert this using 1
      ext y; simp [and_comm]
    · rintro y ⟨hy, hyI⟩
      have hy0 : 0 < y := lt_of_lt_of_le ha hyI.1
      rcases lt_or_eq_of_le (show f y ≤ g y from hy) with hlt | heq
      · have : ∀ᶠ z in 𝓝 y, f z < g z :=
          ((hgc.continuousAt.sub (hfc y hy0)).eventually (lt_mem_nhds (sub_pos.mpr hlt))).mono
            fun z hz => sub_pos.mp hz
        exact mem_nhdsWithin_of_mem_nhds (this.mono fun z hz => le_of_lt hz)
      · have hfy : 0 < f y := lt_of_lt_of_le hδ (heq ▸ le_max_left _ _)
        have hev : ∀ᶠ z in 𝓝 y, 0 < f z := (hfc y hy0).eventually (lt_mem_nhds hfy)
        obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hev
        refine mem_of_superset (Ioo_mem_nhdsGT (show y < y + η by linarith)) fun z hz => ?_
        obtain ⟨M, -, hM⟩ := hbound y z hy0.le hz.1
        have hdec := rgd_decrease f y z M ε hy0 hz.1
          (hcont.mono fun w hw => lt_of_lt_of_le hy0 hw.1) hM
          (fun w hw => hball (by
            rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hw.1, hw.2, hz.2]))
          hdrift
        show f z ≤ g z
        rw [heq] at hdec
        simp only [hg] at hdec ⊢
        rcases le_total δ (C - ε * y) with hm | hm
        · rw [max_eq_right hm] at hdec
          exact le_trans (by linarith) (le_max_right _ _)
        · rw [max_eq_left hm] at hdec
          have : 0 ≤ ε * (z - y) := mul_nonneg hε (by linarith [hz.1])
          exact le_trans (by linarith) (le_max_left _ _)
  exact hsub ⟨hx, le_rfl⟩


theorem rgd_extinction
    (f : ℝ → ℝ) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hbound : ∀ a b : ℝ, 0 ≤ a → a < b → ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Set.Ico a b, rgDini f t ≤ (M : EReal))
    (ε : ℝ) (hε : 0 < ε)
    (hdrift : ∀ᵐ t, 0 ≤ t → 0 < f t → rgDini f t ≤ ((-ε : ℝ) : EReal)) :
    ∀ t : ℝ, f 0 / ε ≤ t → f t = 0 := by
  intro t ht
  have hf0 := hnonneg 0 le_rfl
  have ht0 : 0 ≤ t := le_trans (div_nonneg hf0 hε.le) ht
  have hft : f 0 ≤ ε * t := by rwa [div_le_iff₀ hε, mul_comm] at ht
  refine le_antisymm ?_ (hnonneg t ht0)
  rcases eq_or_lt_of_le ht0 with h0 | htpos
  · subst h0; linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨M0, hM0, hD0⟩ := hbound 0 1 le_rfl one_pos
  have hD : rgDini f 0 < ((M0 + 1 : ℝ) : EReal) :=
    lt_of_le_of_lt (hD0 0 ⟨le_rfl, one_pos⟩) (EReal.coe_lt_coe_iff.mpr (by linarith))
  have e1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), (((f (0 + h) - f 0) / h : ℝ) : EReal) < ((M0 + 1 : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt hD
  set K := M0 + 1 + ε with hK
  have hKpos : 0 < K := by linarith
  set c := min t (η / (2 * K)) with hc
  have hcpos : 0 < c := lt_min htpos (by positivity)
  obtain ⟨a, ha1, ha2⟩ := (e1.and (Ioo_mem_nhdsGT hcpos)).exists
  have hapos : 0 < a := ha2.1
  rw [EReal.coe_lt_coe_iff, zero_add, div_lt_iff₀ hapos] at ha1
  have hfa : f a ≤ max (η / 2) (f 0 + (M0 + 1) * a + ε * a - ε * a) :=
    le_trans (by linarith) (le_max_right _ _)
  have key := rgd_induct f hcont hbound ε hε.le hdrift a (η / 2) (f 0 + (M0 + 1) * a + ε * a) hapos
    (by positivity) hfa t (le_trans ha2.2.le (min_le_left _ _))
  have hac : a * K ≤ η / 2 := by
    have : a ≤ η / (2 * K) := le_trans ha2.2.le (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have : f 0 + (M0 + 1) * a + ε * a - ε * t ≤ η / 2 := by nlinarith
  have := max_le (le_refl (η / 2)) this
  linarith


theorem rg_predsum {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (succ : Fin I → Option (Fin I))
    (hP : ∀ i j, P i j = if succ i = some j then 1 else 0)
    (hinj : ∀ i i' j, succ i = some j → succ i' = some j → i = i') (u : Fin I → ℝ) (j : Fin I) :
    (∃ i0, succ i0 = some j ∧ ∑ i, P i j * u i = u i0) ∨
      ((∀ i, succ i ≠ some j) ∧ ∑ i, P i j * u i = 0) := by
  by_cases h : ∃ i0, succ i0 = some j
  · obtain ⟨i0, hi0⟩ := h
    left
    refine ⟨i0, hi0, ?_⟩
    rw [Finset.sum_eq_single i0]
    · simp [hP, hi0]
    · intro i _ hne
      have : succ i ≠ some j := fun h' => hne (hinj _ _ _ h' hi0)
      simp [hP, this]
    · simp
  · right
    push_neg at h
    exact ⟨h, Finset.sum_eq_zero fun i _ => by simp [hP, h i]⟩

theorem rg_mv {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (u : Fin I → ℝ) (j : Fin I) :
    ((1 - P.transpose).mulVec u) j = u j - ∑ i, P i j * u i := by
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, sub_mul, Finset.sum_sub_distrib,
    Matrix.one_apply]

theorem rg_fix {I : ℕ} (P Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse P Q)
    (z : Fin I → ℝ) (j : Fin I) :
    (Q.mulVec z) j = z j + ∑ i, P i j * (Q.mulVec z) i := by
  have h : (1 - P.transpose).mulVec (Q.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec, hQ.2, Matrix.one_mulVec]
  have := congrFun h j
  rw [rg_mv] at this
  linarith

theorem rg_nonneg {I : ℕ} (P Q : Matrix (Fin I) (Fin I) ℝ) (succ : Fin I → Option (Fin I))
    (hP : ∀ i j, P i j = if succ i = some j then 1 else 0)
    (hinj : ∀ i i' j, succ i = some j → succ i' = some j → i = i')
    (hQ : IsRoutingInverse P Q) (z : Fin I → ℝ) (hz : ∀ j, 0 ≤ z j) :
    ∀ j, 0 ≤ (Q.mulVec z) j := by
  set y := Q.mulVec z with hy
  by_contra hneg
  push_neg at hneg
  obtain ⟨j0, hj0⟩ := hneg
  obtain ⟨jm, -, hjm⟩ := Finset.exists_min_image Finset.univ y ⟨j0, Finset.mem_univ _⟩
  have hm : y jm < 0 := lt_of_le_of_lt (hjm j0 (Finset.mem_univ _)) hj0
  set v : Fin I → ℝ := fun j => if y j = y jm then 1 else 0 with hv
  have hvnn : ∀ j, 0 ≤ v j := fun j => by simp only [hv]; split_ifs <;> norm_num
  have hPnn : ∀ i j, 0 ≤ P i j := fun i j => by rw [hP]; split_ifs <;> norm_num
  have hw_le : ∀ j, v j - ∑ i, P i j * v i ≤ 0 := by
    intro j
    by_cases hj : y j = y jm
    · have hfix := rg_fix P Q hQ z j
      rcases rg_predsum P succ hP hinj y j with ⟨i0, hi0, hs⟩ | ⟨hno, hs⟩
      · have hy0 : y i0 = y jm :=
          le_antisymm (by rw [← hy] at hfix; linarith [hz j]) (hjm i0 (Finset.mem_univ _))
        rcases rg_predsum P succ hP hinj v j with ⟨i1, hi1, hs'⟩ | ⟨hno', hs'⟩
        · have : i1 = i0 := hinj _ _ _ hi1 hi0
          subst this
          rw [hs']
          simp [hv, hj, hy0]
        · exact absurd hi0 (hno' i0)
      · rw [← hy] at hfix
        linarith [hz j]
    · have : 0 ≤ ∑ i, P i j * v i := Finset.sum_nonneg fun i _ => mul_nonneg (hPnn i j) (hvnn i)
      have hvj : v j = 0 := by simp [hv, hj]
      linarith
  have hsum : 0 ≤ ∑ j, (v j - ∑ i, P i j * v i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [← Finset.sum_mul]
    have h1 : ∑ j, P i j ≤ 1 := by
      cases h : succ i with
      | none => simp [hP, h]
      | some j0 => simp [hP, h]
    nlinarith [hvnn i]
  have hw0 : ∀ j, v j - ∑ i, P i j * v i = 0 := by
    have hle : ∑ j, (v j - ∑ i, P i j * v i) ≤ 0 := Finset.sum_nonpos fun j _ => hw_le j
    have := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hw_le j)).mp (le_antisymm hle hsum)
    exact fun j => this j (Finset.mem_univ _)
  have hzero : (1 - P.transpose).mulVec v = 0 := by
    funext j; rw [rg_mv]; exact hw0 j
  have hv0 : v = 0 := by
    have : Q.mulVec ((1 - P.transpose).mulVec v) = v := by
      rw [Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec]
    rw [← this, hzero, Matrix.mulVec_zero]
  have := congrFun hv0 jm
  simp [hv] at this

theorem rg_ge {I : ℕ} (P Q : Matrix (Fin I) (Fin I) ℝ) (succ : Fin I → Option (Fin I))
    (hP : ∀ i j, P i j = if succ i = some j then 1 else 0)
    (hinj : ∀ i i' j, succ i = some j → succ i' = some j → i = i')
    (hQ : IsRoutingInverse P Q) (z : Fin I → ℝ) (hz : ∀ j, 0 ≤ z j) (j : Fin I) :
    z j ≤ (Q.mulVec z) j := by
  rw [rg_fix P Q hQ z j]
  have hPnn : ∀ i j, 0 ≤ P i j := fun i j => by rw [hP]; split_ifs <;> norm_num
  have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
    mul_nonneg (hPnn i j) (rg_nonneg P Q succ hP hinj hQ z hz i)
  linarith

theorem rg_fin {K : ℕ} [NeZero K] (a b : Fin K) (h : ((a : ℕ) + 1) % K = (b : ℕ)) : a = b - 1 := by
  have : a + 1 = b := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod, h]
  exact eq_sub_of_add_eq this

theorem rg_pool {I K : ℕ} [NeZero K] (dat : QueueingNetworkData I K) (succ : Fin I → Option (Fin I))
    (hring : IsUnidirectionalRing dat succ) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q) (z : Fin I → ℝ) (hz : ∀ j, 0 ≤ z j) (k : Fin K) :
    ∑ j ∈ poolBuffers dat k, (Q.mulVec z) j ≤
      ∑ j ∈ poolBuffers dat (k - 1), (Q.mulVec z) j + ∑ j ∈ poolBuffers dat k, z j := by
  obtain ⟨hP, hstep, hinj, -, -, -⟩ := hring
  have hy := rg_nonneg dat.P Q succ hP hinj hQ z hz
  rw [Finset.sum_congr rfl fun j _ => rg_fix dat.P Q hQ z j, Finset.sum_add_distrib, add_comm]
  gcongr
  rw [Finset.sum_comm]
  unfold poolBuffers
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_mul, Finset.sum_filter]
  cases h : succ i with
  | none => simp [hP, h]; split_ifs <;> simp [hy i]
  | some j0 =>
    simp only [hP, h, Option.some.injEq]
    rw [Finset.sum_eq_single j0 (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    by_cases hj0 : dat.p j0 = k
    · have := rg_fin (dat.p i) k (by rw [← hj0]; exact hstep i j0 h)
      simp [hj0, this]
    · simp only [Finset.mem_univ, if_true, hj0, if_false, zero_mul]
      split_ifs <;> simp [hy i]


theorem rg_dini_le (f : ℝ → ℝ) (t c : ℝ)
    (h : ∀ᶠ s in 𝓝[>] (0:ℝ), f (t + s) - f t ≤ c * s) : rgDini f t ≤ (c : EReal) := by
  unfold rgDini
  refine Filter.limsup_le_of_le (h := ?_)
  filter_upwards [h, self_mem_nhdsWithin] with s hs hs0
  have hs0' : (0:ℝ) < s := hs0
  rw [EReal.coe_le_coe_iff, div_le_iff₀ hs0']
  linarith

open Fin.NatCast in
theorem rg_core {I K : ℕ} (dat : QueueingNetworkData I K) (succ : Fin I → Option (Fin I))
    (hring : IsUnidirectionalRing dat succ)
    (hm : ∀ i, 0 < dat.m i)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    FluidModelGloballyStable dat := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    refine ⟨1, one_pos, fun Dh Fh Th Zh _ t _ => ?_⟩
    funext j; exact (dat.p j).elim0
  haveI : NeZero K := ⟨by omega⟩
  have hring' := hring
  obtain ⟨hP, hstep, hinj, hlam0, hmeq, hb⟩ := hring
  set α := Q.mulVec dat.lam with hα
  set a : Fin K → ℝ := fun k => ∑ j ∈ poolBuffers dat k, α j with ha
  have hpool : ∀ k j, j ∈ poolBuffers dat k ↔ dat.p j = k := fun k j => by simp [poolBuffers]
  have hmem : ∀ j, j ∈ poolBuffers dat (dat.p j) := fun j => (hpool _ _).mpr rfl
  have hεj : ∀ j, 0 < 1 / dat.m j - a (dat.p j) := by
    intro j
    have hl := hload (dat.p j)
    rw [hb] at hl
    unfold workloadOperator at hl
    have : ∑ i ∈ poolBuffers dat (dat.p j), dat.m i * (Q.mulVec dat.lam) i
        = dat.m j * a (dat.p j) := by
      simp only [ha, Finset.mul_sum, hα]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hmeq i j ((hpool _ _).mp hi)]
    rw [this] at hl
    rw [sub_pos, lt_div_iff₀ (hm j)]; linarith
  obtain ⟨ε, hε, hεle⟩ : ∃ ε > 0, ∀ j, ε ≤ 1 / dat.m j - a (dat.p j) := by
    rcases isEmpty_or_nonempty (Fin I) with hI | hI
    · exact ⟨1, one_pos, fun j => isEmptyElim j⟩
    · obtain ⟨j1, -, hj1⟩ := Finset.exists_min_image Finset.univ
        (fun j => 1 / dat.m j - a (dat.p j)) Finset.univ_nonempty
      exact ⟨_, hεj j1, fun j => hj1 j (Finset.mem_univ _)⟩
  set B : ℝ := ∑ j, ∑ i, |Q j i| + 1 with hB
  have hB0 : 0 ≤ ∑ j, ∑ i, |Q j i| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hQB : ∀ j i, Q j i ≤ B := fun j i => by
    have h1 : |Q j i| ≤ ∑ i', |Q j i'| :=
      Finset.single_le_sum (f := fun i' => |Q j i'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : ∑ i', |Q j i'| ≤ ∑ j', ∑ i', |Q j' i'| :=
      Finset.single_le_sum (f := fun j' => ∑ i', |Q j' i'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    linarith [le_abs_self (Q j i)]
  have hBpos : 0 < B := by linarith
  set M : ℝ := ∑ k, |a k| + 1 with hM
  have haM : ∀ k, a k ≤ M := fun k => by
    have : |a k| ≤ ∑ k', |a k'| :=
      Finset.single_le_sum (f := fun k' => |a k'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    linarith [le_abs_self (a k)]
  have hMpos : 0 < M := by
    have : 0 ≤ ∑ k, |a k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  refine ⟨2 * ((I : ℝ) * B + 1) / ε, by positivity, ?_⟩
  intro Dh Fh Th Zh hsol t ht
  obtain ⟨⟨h1, h2, h3, h4, ⟨hT0, hTmono⟩, hcap⟩, hni⟩ := hsol
  have hZ0 : ∀ j, 0 ≤ Zh 0 j := h2 0 le_rfl
  have hsum0 : 0 ≤ ∑ i, Zh 0 i := Finset.sum_nonneg fun i _ => hZ0 i
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hF : ∀ s, 0 ≤ s → ∀ j, Fh s j = Th s j / dat.m j := fun s hs j => by
    rw [← h4 s hs j]; field_simp [(hm j).ne']
  have hQZ : ∀ s, 0 ≤ s → Q.mulVec (Zh s) = Q.mulVec (Zh 0) + s • α - Fh s := by
    intro s hs
    have hZ : Zh s = Zh 0 + s • dat.lam - (1 - dat.P.transpose).mulVec (Fh s) := by
      ext i
      rw [h1 s hs i, h3 s hs i]
      simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      ring
    rw [hZ, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      hQ.1, Matrix.one_mulVec]
  set Vf : Fin K → ℝ → ℝ := fun k s => ∑ j ∈ poolBuffers dat k, (Q.mulVec (Zh 0)) j + a k * s
    - ∑ j ∈ poolBuffers dat k, Th s j / dat.m j with hVf
  have hVeq : ∀ k s, 0 ≤ s → Vf k s = ∑ j ∈ poolBuffers dat k, (Q.mulVec (Zh s)) j := by
    intro k s hs
    rw [hQZ s hs]
    simp only [hVf, ha, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => hF s hs j)]
    ring
  have hVnn : ∀ k s, 0 ≤ s → 0 ≤ Vf k s := fun k s hs => by
    rw [hVeq k s hs]
    exact Finset.sum_nonneg fun j _ => rg_nonneg dat.P Q succ hP hinj hQ _ (h2 s hs) j
  have hVN : ∀ k s, 0 ≤ s → ∑ j ∈ poolBuffers dat k, Zh s j ≤ Vf k s := fun k s hs => by
    rw [hVeq k s hs]
    exact Finset.sum_le_sum fun j _ => rg_ge dat.P Q succ hP hinj hQ _ (h2 s hs) j
  have hVpool : ∀ k s, 0 ≤ s → Vf k s ≤ Vf (k - 1) s + ∑ j ∈ poolBuffers dat k, Zh s j :=
    fun k s hs => by
      rw [hVeq k s hs, hVeq (k - 1) s hs]
      exact rg_pool dat succ hring' Q hQ _ (h2 s hs) k
  have hTmon : ∀ j, Monotone (fun s => Th s j) := fun j x y h => hTmono h j
  have hTinc : ∀ s r, 0 ≤ s → s ≤ r → ∀ j, Th r j - Th s j ≤ r - s := by
    intro s r hs hsr j
    have hc := hcap s r hs hsr (dat.p j)
    rw [hb, one_mul] at hc
    have := Finset.single_le_sum (f := fun i => Th r i - Th s i)
      (fun i _ => sub_nonneg.mpr (hTmono hsr i)) (hmem j)
    linarith
  have hTc : ∀ j, ContinuousOn (fun s => Th s j) (Ici 0) := by
    intro j
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun x hx y hy => ?_).continuousOn
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    rcases le_total x y with hxy | hxy
    · have := hTinc x y hx hxy j
      have := hTmon j hxy
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have := hTinc y x hy hxy j
      have := hTmon j hxy
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hVc : ∀ k, ContinuousOn (Vf k) (Ioi 0) := fun k =>
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).sub
      (continuousOn_finset_sum _ fun j _ => ((hTc j).mono Ioi_subset_Ici_self).div_const _)
  have hVup : ∀ k s r, 0 ≤ s → s ≤ r → Vf k r ≤ Vf k s + M * (r - s) := by
    intro k s r hs hsr
    have : ∑ j ∈ poolBuffers dat k, Th s j / dat.m j ≤ ∑ j ∈ poolBuffers dat k, Th r j / dat.m j :=
      Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hTmon j hsr) (hm j).le
    have h2' : a k * (r - s) ≤ M * (r - s) := mul_le_mul_of_nonneg_right (haM k) (by linarith)
    simp only [hVf]
    nlinarith
  set f : ℝ → ℝ := fun s => Finset.univ.sup' Finset.univ_nonempty (fun k => Vf k s) with hf
  have hle : ∀ k s, Vf k s ≤ f s := fun k s => Finset.le_sup' (fun k => Vf k s) (Finset.mem_univ k)
  have hfnn : ∀ s, 0 ≤ s → 0 ≤ f s := fun s hs => le_trans (hVnn 0 s hs) (hle 0 s)
  have hfc : ContinuousOn f (Ioi 0) := ContinuousOn.finset_sup'_apply _ (fun k _ => hVc k)
  have hfup : ∀ s h, 0 ≤ s → 0 ≤ h → f (s + h) ≤ f s + M * h := by
    intro s h hs hh
    refine Finset.sup'_le _ _ fun k _ => ?_
    have := hVup k s (s + h) hs (by linarith)
    have := hle k s
    simp only [add_sub_cancel_left] at *
    linarith
  have hbound : ∀ a b : ℝ, 0 ≤ a → a < b →
      ∃ M' : ℝ, 0 < M' ∧ ∀ t ∈ Ico a b, rgDini f t ≤ (M' : EReal) := by
    intro a' b' ha' _
    refine ⟨M, hMpos, fun s hs => rg_dini_le f s M ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    have := hfup s h (ha'.trans hs.1) (le_of_lt hh)
    linarith
  -- drift
  have hdrift : ∀ᵐ s, 0 ≤ s → 0 < f s → rgDini f s ≤ ((-(ε / 2) : ℝ) : EReal) := by
    have hdiff : ∀ᵐ s, ∀ j, DifferentiableAt ℝ (fun s => Th s j) s :=
      ae_all_iff.mpr fun j => (hTmon j).ae_differentiableAt
    filter_upwards [hdiff, compl_mem_ae_iff.mpr (measure_singleton (0:ℝ))] with s hs hs0 hsnn hfpos
    have hspos : 0 < s := lt_of_le_of_ne hsnn (Ne.symm hs0)
    set τ : Fin I → ℝ := fun j => deriv (fun s => Th s j) s with hτdef
    have hτ : ∀ j, HasDerivAt (fun s => Th s j) (τ j) s := fun j => (hs j).hasDerivAt
    set d : Fin K → ℝ := fun k => a k - ∑ j ∈ poolBuffers dat k, τ j / dat.m j with hd
    have hdV : ∀ k, HasDerivAt (Vf k) (d k) s := by
      intro k
      have e1 := ((hasDerivAt_id s).const_mul (a k)).const_add
        (∑ j ∈ poolBuffers dat k, (Q.mulVec (Zh 0)) j)
      have e2 := HasDerivAt.fun_sum (u := poolBuffers dat k) (A := fun j r => Th r j / dat.m j)
        (A' := fun j => τ j / dat.m j) (x := s) fun j _ => (hτ j).div_const (dat.m j)
      have e3 := e1.sub e2
      exact e3.congr_deriv (by simp [hd])
    set Zf : Fin I → ℝ → ℝ := fun j r => Zh 0 j + dat.lam j * r
      + ∑ i, dat.P i j * (Th r i / dat.m i) - Th r j / dat.m j with hZf
    have hZeq : ∀ j r, 0 ≤ r → Zh r j = Zf j r := by
      intro j r hr
      rw [h1 r hr j, h3 r hr j, hF r hr j]
      simp only [hZf]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by rw [hF r hr i]
    set zd : Fin I → ℝ := fun j => dat.lam j + ∑ i, dat.P i j * (τ i / dat.m i) - τ j / dat.m j
      with hzd
    have hdZ : ∀ j, HasDerivAt (Zf j) (zd j) s := by
      intro j
      have e1 := ((hasDerivAt_id s).const_mul (dat.lam j)).const_add (Zh 0 j)
      have e2 := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i r => dat.P i j * (Th r i / dat.m i))
        (A' := fun i => dat.P i j * (τ i / dat.m i)) (x := s)
        fun i _ => ((hτ i).div_const (dat.m i)).const_mul (dat.P i j)
      have e3 := (e1.add e2).sub ((hτ j).div_const (dat.m j))
      exact e3.congr_deriv (by simp [hzd])
    set Nf : Fin K → ℝ → ℝ := fun k r => ∑ j ∈ poolBuffers dat k, Zf j r with hNf
    have hdN : ∀ k, HasDerivAt (Nf k) (∑ j ∈ poolBuffers dat k, zd j) s := by
      intro k
      exact HasDerivAt.fun_sum (u := poolBuffers dat k) (A := fun j r => Zf j r)
        (A' := zd) (x := s) fun j _ => hdZ j
    have hNeq : ∀ k r, 0 ≤ r → Nf k r = ∑ j ∈ poolBuffers dat k, Zh r j := fun k r hr =>
      Finset.sum_congr rfl fun j _ => (hZeq j r hr).symm
    have hev : ∀ᶠ r in 𝓝 s, 0 ≤ r := (lt_mem_nhds hspos).mono fun r hr => le_of_lt hr
    set Fv := f s with hFv
    have hstepS : ∀ k, Vf k s = Fv → -ε < d k →
        (Vf (k - 1) s = Fv ∧ -ε < d (k - 1)) ∧ Nf k s = 0 := by
      intro k hkF hkd
      have hNnn : 0 ≤ Nf k s := by
        rw [hNeq k s hsnn]; exact Finset.sum_nonneg fun j _ => h2 s hsnn j
      have hN0 : Nf k s = 0 := by
        by_contra hne
        have hpos : 0 < ∑ j ∈ poolBuffers dat k, Zh s j := by
          rw [← hNeq k s hsnn]; exact lt_of_le_of_ne hNnn (Ne.symm hne)
        have hsumτ := hni k s hspos hpos (∑ j ∈ poolBuffers dat k, τ j)
          (HasDerivAt.fun_sum (u := poolBuffers dat k) (A := fun j r => Th r j) (A' := τ) (x := s)
            fun j _ => hτ j)
        obtain ⟨j0, hj0⟩ : (poolBuffers dat k).Nonempty :=
          Finset.nonempty_of_sum_ne_zero hpos.ne'
        have hpj0 : dat.p j0 = k := (hpool _ _).mp hj0
        have hsum1 : ∑ j ∈ poolBuffers dat k, τ j / dat.m j = 1 / dat.m j0 := by
          rw [Finset.sum_congr rfl (fun j hj => by
            rw [hmeq j j0 (((hpool _ _).mp hj).trans hpj0.symm)]), ← Finset.sum_div, hsumτ, hb]
        have := hεle j0
        rw [hpj0] at this
        have : d k = a k - 1 / dat.m j0 := by simp only [hd]; rw [hsum1]
        linarith
      have hk1F : Vf (k - 1) s = Fv := by
        refine le_antisymm (hle _ _) ?_
        have := hVpool k s hsnn
        rw [← hNeq k s hsnn, hN0] at this
        linarith
      have hmax : IsLocalMax (fun r => Vf k r - Vf (k - 1) r - Nf k r) s := by
        filter_upwards [hev] with r hr
        have := hVpool k r hr
        rw [← hNeq k r hr] at this
        show Vf k r - Vf (k - 1) r - Nf k r ≤ Vf k s - Vf (k - 1) s - Nf k s
        rw [hkF, hk1F, hN0]
        linarith
      have hmin : IsLocalMin (Nf k) s := by
        filter_upwards [hev] with r hr
        rw [hN0, hNeq k r hr]
        exact Finset.sum_nonneg fun j _ => h2 r hr j
      have e1 := hmax.hasDerivAt_eq_zero (((hdV k).sub (hdV (k - 1))).sub (hdN k))
      have e2 := hmin.hasDerivAt_eq_zero (hdN k)
      exact ⟨⟨hk1F, by linarith⟩, hN0⟩
    have key : ∀ k, Vf k s = Fv → d k ≤ -ε := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨k0, hk0F, hk0d⟩ := hcon
      have hall : ∀ n : ℕ, Vf (k0 - (n : Fin K)) s = Fv ∧ -ε < d (k0 - (n : Fin K)) := by
        intro n
        induction n with
        | zero => simpa using ⟨hk0F, hk0d⟩
        | succ n ih =>
          have := (hstepS _ ih.1 ih.2).1
          rwa [Nat.cast_succ, ← sub_sub]
      have hallk : ∀ k, Vf k s = Fv ∧ -ε < d k := fun k => by
        have := hall (k0 - k).val
        rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this
      have hZs0 : ∀ j, Zh s j = 0 := by
        intro j
        have hN := (hstepS _ (hallk (dat.p j)).1 (hallk (dat.p j)).2).2
        rw [hNeq _ s hsnn] at hN
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h2 s hsnn i)).mp hN j (hmem j)
      have hV0 : Vf k0 s = 0 := by
        rw [hVeq k0 s hsnn]
        have : Zh s = 0 := funext hZs0
        rw [this, Matrix.mulVec_zero]
        simp
      linarith
    refine rg_dini_le f s _ ?_
    have hall : ∀ k, ∀ᶠ h in 𝓝[>] (0:ℝ), Vf k (s + h) ≤ Fv - ε / 2 * h := by
      intro k
      by_cases hkF : Vf k s = Fv
      · have hdk := key k hkF
        have ht := (hdV k).tendsto_slope_zero_right
        filter_upwards [ht.eventually (gt_mem_nhds (show d k < -(ε / 2) by linarith)),
          self_mem_nhdsWithin] with h hh hh0
        have hh0' : (0:ℝ) < h := hh0
        rw [smul_eq_mul, inv_mul_lt_iff₀ hh0'] at hh
        linarith
      · have hlt : Vf k s < Fv := lt_of_le_of_ne (hle k s) hkF
        have hδ : 0 < (Fv - Vf k s) / (M + ε / 2) := div_pos (by linarith) (by linarith)
        filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
        have hh1 : 0 < h := hh.1
        have hh2 : h < (Fv - Vf k s) / (M + ε / 2) := hh.2
        have := hVup k s (s + h) hsnn (by linarith)
        simp only [add_sub_cancel_left] at this
        rw [lt_div_iff₀ (by linarith)] at hh2
        nlinarith
    filter_upwards [Filter.eventually_all.mpr hall] with h hh
    have : f (s + h) ≤ Fv - ε / 2 * h := Finset.sup'_le _ _ fun k _ => hh k
    linarith
  have hext := rgd_extinction f hfnn hfc hbound (ε / 2) (by positivity) hdrift
  have hf0 : f 0 ≤ (I : ℝ) * B * ∑ i, Zh 0 i := by
    refine Finset.sup'_le _ _ fun k _ => ?_
    rw [hVeq k 0 le_rfl]
    have hy := rg_nonneg dat.P Q succ hP hinj hQ _ hZ0
    calc ∑ j ∈ poolBuffers dat k, (Q.mulVec (Zh 0)) j ≤ ∑ j, (Q.mulVec (Zh 0)) j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hy j
      _ ≤ ∑ j : Fin I, ∑ i, B * Zh 0 i := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hQB j i) (hZ0 i)
      _ = (I : ℝ) * B * ∑ i, Zh 0 i := by
          simp [Finset.sum_const, ← Finset.mul_sum]; ring
  have htf : f 0 / (ε / 2) ≤ t := by
    rw [div_le_iff₀ (by positivity)]
    have : 2 * ((I : ℝ) * B + 1) / ε * (∑ i, Zh 0 i) * (ε / 2)
        = ((I : ℝ) * B + 1) * ∑ i, Zh 0 i := by
      field_simp
    have h' := mul_le_mul_of_nonneg_right ht (show 0 ≤ ε / 2 by positivity)
    nlinarith
  have hft := hext t htf
  funext j
  have e1 := hVN (dat.p j) t ht0
  have e2 := hle (dat.p j) t
  have e3 := Finset.single_le_sum (f := fun i => Zh t i) (fun i _ => h2 t ht0 i) (hmem j)
  have e4 := h2 t ht0 j
  linarith

end ProcessingNetworks.GlobalStability

open ProcessingNetworks.GlobalStability


theorem solution
    {I K : ℕ} (dat : QueueingNetworkData I K) (succ : Fin I → Option (Fin I))
    (hring : IsUnidirectionalRing dat succ)
    (hlam : ∀ i, 0 ≤ dat.lam i) (hm : ∀ i, 0 < dat.m i)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    FluidModelGloballyStable dat := by
  exact rg_core dat succ hring hm Q hQ hload
