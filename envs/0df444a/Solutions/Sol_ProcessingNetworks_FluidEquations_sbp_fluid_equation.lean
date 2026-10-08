-- Prove2me | solution 1 for ProcessingNetworks.FluidEquations.sbp_fluid_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:49:56.721983+00:00
-- url     : https://prove2.me/submissions/c3c585b7-d278-49c0-9c1d-8048dc39c119

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidEquations_ProcessFamily
import Definitions.Def_ProcessingNetworks_FluidEquations_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FluidEquations_Hset
import Definitions.Def_ProcessingNetworks_FluidEquations_PolicyRelations



namespace ProcessingNetworks.FluidEquations

open MeasureTheory Filter ProcessingNetworks.Stability

lemma fe_uoc_sum {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ}
    (h : UOCConverges f g) (S : Finset (Fin d)) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ Nb : ℕ, ∀ n ≥ Nb, ∀ t ∈ Set.Icc (0:ℝ) T,
      |∑ i ∈ S, f n t i - ∑ i ∈ S, g t i| < ε := by
  intro T hT ε hε
  obtain ⟨Nb, hN⟩ := h T hT (ε / (S.card + 1)) (by positivity)
  refine ⟨Nb, fun n hn t ht => ?_⟩
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i ∈ S, |f n t i - g t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, ε / (S.card + 1) := Finset.sum_le_sum (fun i _ => (hN n hn t ht i).le)
    _ < ε := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

lemma fe_uoc_sum_tendsto {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ}
    (h : UOCConverges f g) (S : Finset (Fin d)) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => ∑ i ∈ S, f n t i) atTop (nhds (∑ i ∈ S, g t i)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Nb, hN⟩ := fe_uoc_sum h S t ht ε hε
  exact ⟨Nb, fun n hn => by rw [Real.dist_eq]; exact hN n hn t ⟨ht, le_rfl⟩⟩

lemma fe_deriv_of_affine (G : ℝ → ℝ) (a c t b : ℝ) (hat : a < t) (htc : t < c)
    (h : ∀ u1 u2, a < u1 → u1 ≤ u2 → u2 < c → G u2 - G u1 = (u2 - u1) * b) :
    HasDerivAt G b t := by
  have h0 : HasDerivAt (fun s => G t + (s - t) * b) b t := by
    have := (((hasDerivAt_id t).sub_const t).mul_const b).const_add (G t)
    simpa using this
  apply h0.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hat htc] with s hs
  rcases le_total s t with hst | hst
  · have := h s t hs.1 hst htc; linarith
  · have := h t s hat hst hs.2; linarith

lemma fe_lim_bounds {A B e : ℕ → ℝ} {a b' L : ℝ} (hA : Tendsto A atTop (nhds a))
    (hB : Tendsto B atTop (nhds b')) (he : Tendsto e atTop (nhds 0))
    (hev : ∀ᶠ n in atTop, L - e n ≤ A n - B n ∧ A n - B n ≤ L) : a - b' = L := by
  have hAB : Tendsto (fun n => A n - B n) atTop (nhds (a - b')) := hA.sub hB
  apply le_antisymm
  · exact le_of_tendsto hAB (hev.mono fun n h => h.2)
  · have hL : Tendsto (fun n => L - e n) atTop (nhds (L - 0)) := tendsto_const_nhds.sub he
    have := le_of_tendsto_of_tendsto hL hAB (hev.mono fun n h => h.1)
    simpa using this

/-- Local positivity window: from continuity and positivity of the limit sum we get an interval
on which, eventually, the unscaled sum exceeds any given level. -/
lemma fe_window {d : ℕ} (S : Finset (Fin d)) (Zh : ℝ → Fin d → ℝ) (hZcont : Continuous Zh)
    (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ S, Zh t i) :
    ∃ a c δ : ℝ, 0 < a ∧ a < t ∧ t < c ∧ 0 < δ ∧
      ∀ u, a < u → u < c → δ < ∑ i ∈ S, Zh u i := by
  have hcont : Continuous fun u => ∑ i ∈ S, Zh u i :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).comp hZcont)
  have hev : ∀ᶠ u in nhds t, (∑ i ∈ S, Zh t i) / 2 < ∑ i ∈ S, Zh u i :=
    hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨t - min ε t / 2, t + min ε t / 2, (∑ i ∈ S, Zh t i) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · have := min_le_right ε t; linarith
  · have : 0 < min ε t := lt_min hε ht; linarith
  · have : 0 < min ε t := lt_min hε ht; linarith
  · linarith
  · intro u h1 h2
    apply hball
    rw [Real.dist_eq, abs_lt]
    have := min_le_left ε t
    constructor <;> linarith

/-- Generic: eventually the scaled sum stays above `δ/2` on `[0,c]`, so the unscaled sum exceeds
`size * δ / 2`. -/
lemma fe_unscaled_big {d : ℕ} (S : Finset (Fin d)) (Zx : ℕ → ℝ → Fin d → ℝ) (s : ℕ → ℝ)
    (Zh : ℝ → Fin d → ℝ)
    (hZ : UOCConverges (fun n t i => (s n)⁻¹ * Zx n (s n * t) i) Zh)
    (hs : Tendsto s atTop atTop) (a c δ L : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (hwin : ∀ u, a < u → u < c → δ < ∑ i ∈ S, Zh u i) :
    ∀ᶠ n in atTop, 0 < s n ∧ ∀ u1 u2, a < u1 → u1 ≤ u2 → u2 < c → ∀ w ∈ Set.Icc (s n * u1) (s n * u2),
      L < ∑ i ∈ S, Zx n w i := by
  have hc : 0 ≤ c ∨ c < 0 := le_or_gt 0 c
  rcases hc with hc | hc
  swap
  · filter_upwards [hs.eventually_ge_atTop 1] with n hn
    refine ⟨by linarith, fun u1 u2 h1 h12 h2 => ?_⟩
    exfalso; linarith
  obtain ⟨Nb, hN⟩ := fe_uoc_sum hZ S c hc (δ / 2) (by linarith)
  filter_upwards [hs.eventually_ge_atTop (2 * |L| / δ + 1), eventually_ge_atTop Nb]
    with n hn hnb
  have hspos : 0 < s n := by
    have : 0 ≤ 2 * |L| / δ := by positivity
    linarith
  refine ⟨hspos, fun u1 u2 h1 _ h2 w hw => ?_⟩
  have hu1 : u1 ≤ w / s n := by rw [le_div_iff₀ hspos]; linarith [hw.1]
  have hu2 : w / s n ≤ u2 := by rw [div_le_iff₀ hspos]; linarith [hw.2]
  have hb := hN n hnb (w / s n) ⟨by linarith, by linarith⟩
  have hsw : s n * (w / s n) = w := mul_div_cancel₀ w hspos.ne'
  simp only [hsw] at hb
  have hz := hwin (w / s n) (by linarith) (by linarith)
  rw [← Finset.mul_sum] at hb
  have hlow : δ / 2 < (s n)⁻¹ * ∑ i ∈ S, Zx n w i := by
    rw [abs_lt] at hb; linarith [hb.1]
  have h3 : s n * (δ / 2) < ∑ i ∈ S, Zx n w i := by
    have := mul_lt_mul_of_pos_left hlow hspos
    rwa [← mul_assoc, mul_inv_cancel₀ hspos.ne', one_mul] at this
  have h4 : |L| < s n * (δ / 2) := by
    have h5 : (2 * |L| / δ + 1) * (δ / 2) = |L| + δ / 2 := by field_simp
    nlinarith
  linarith [le_abs_self L]


lemma fe_uoc_tendsto {d : ℕ} {f : ℕ → ℝ → Fin d → ℝ} {g : ℝ → Fin d → ℝ}
    (h : UOCConverges f g) (i : Fin d) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => f n t i) atTop (nhds (g t i)) := by
  simpa using fe_uoc_sum_tendsto h {i} t ht

lemma fe_bsup_bdd (f : ℕ → ℝ) (n : ℕ) :
    BddAbove (Set.range fun ℓ => ⨆ (_ : ℓ ∈ Finset.range n), f ℓ) := by
  refine ⟨∑ ℓ ∈ Finset.range n, |f ℓ|, ?_⟩
  rintro y ⟨ℓ, rfl⟩
  exact Real.iSup_le (fun h => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun ℓ => |f ℓ|) (fun i _ => abs_nonneg _) h))
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

lemma fe_le_bsup (f : ℕ → ℝ) {n ℓ : ℕ} (h : ℓ < n) : f ℓ ≤ ⨆ ℓ ∈ Finset.range n, f ℓ := by
  have h' : ℓ ∈ Finset.range n := Finset.mem_range.mpr h
  calc f ℓ = ⨆ (_ : ℓ ∈ Finset.range n), f ℓ := (ciSup_pos (f := fun _ => f ℓ) h').symm
    _ ≤ _ := le_ciSup (f := fun ℓ => ⨆ (_ : ℓ ∈ Finset.range n), f ℓ) (fe_bsup_bdd f n) ℓ

lemma fe_bsup_nonneg (f : ℕ → ℝ) (n : ℕ) : 0 ≤ ⨆ ℓ ∈ Finset.range n, f ℓ := by
  have h0 : (⨆ (_ : n ∈ Finset.range n), f n) = 0 := by
    have : ¬ n ∈ Finset.range n := by simp
    simp [this]
  rw [← h0]
  exact le_ciSup (f := fun ℓ => ⨆ (_ : ℓ ∈ Finset.range n), f ℓ) (fe_bsup_bdd f n) n

lemma fe_bsup_le (f : ℕ → ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ ℓ, ℓ < n → f ℓ ≤ B) :
    ⨆ ℓ ∈ Finset.range n, f ℓ ≤ B :=
  Real.iSup_le (fun ℓ => Real.iSup_le (fun hl => h ℓ (Finset.mem_range.mp hl)) hB) hB

lemma fe_bsup_mono (f : ℕ → ℝ) {n m : ℕ} (h : n ≤ m) :
    ⨆ ℓ ∈ Finset.range n, f ℓ ≤ ⨆ ℓ ∈ Finset.range m, f ℓ :=
  fe_bsup_le f n (fe_bsup_nonneg f m) (fun ℓ hl => fe_le_bsup f (by omega))

lemma fe_dm_le {Ω : Type*} {I : ℕ} (N0 : Fin I → ℕ) (Psi : Fin I → ℕ → Ω → ℝ × (Fin I → ℕ))
    (v : Fin I → ℕ → Ω → ℝ) (φ : Fin I → ℕ → Ω → Fin I → ℕ) (i : Fin I) (n : ℕ) (ω : Ω)
    (pool : Finset (Ω → ℝ × (Fin I → ℕ)))
    (hpool : ∀ k, k < N0 i → (fun ω => Psi i k ω) ∈ pool) :
    delayedMax N0 Psi v φ i n ω ≤
      (∑ p ∈ pool, |(p ω).1|) + ⨆ ℓ ∈ Finset.range n, v i ℓ ω := by
  have hC : 0 ≤ ∑ p ∈ pool, |(p ω).1| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hg := fe_bsup_nonneg (fun ℓ => v i ℓ ω) n
  unfold delayedMax
  apply fe_bsup_le _ _ (add_nonneg hC hg)
  intro k hk
  unfold delayedTerm
  split_ifs with h
  · have := Finset.single_le_sum (f := fun p : Ω → ℝ × (Fin I → ℕ) => |(p ω).1|)
      (fun _ _ => abs_nonneg _) (hpool k h)
    try simp only at this
    linarith [le_abs_self (Psi i k ω).1]
  · have := fe_le_bsup (fun ℓ => v i ℓ ω) (show k - N0 i < n by omega)
    simp only at this ⊢
    linarith

theorem sbp_core
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ)
    (σ : Equiv.Perm (Fin I)) (hsbp : SBPNonPreemptive dat σ fam)
    (ω : Ω) (x : ℕ → Xstate) (Fh Th Zh : ℝ → Fin I → ℝ)
    (h638 : ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v i ℓ ω) atTop (nhds 0))
    (hZcont : Continuous Zh) (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hF : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω i : ℝ)) Fh)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh)
    (j : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ Hset dat σ j, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ Hset dat σ j, Th s i) (dat.b (dat.p j)) t := by
  set S := Hset dat σ j with hS
  set b := dat.b (dat.p j) with hbdef
  have hb : 0 < b := dat.b_pos _
  obtain ⟨a, c, δ, ha, hat, htc, hδ, hwin⟩ := fe_window S Zh hZcont t ht hz
  apply fe_deriv_of_affine _ a c t _ hat htc
  intro u1 u2 h1 h12 h2
  have hu1 : 0 ≤ u1 := by linarith
  obtain ⟨κ, hκ⟩ := fam.service_bound
  set C : ℝ := ∑ p ∈ fam.pool, |(p ω).1| with hCdef
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  set g : Fin I → ℕ → ℝ := fun i n => ⨆ ℓ ∈ Finset.range n, v i ℓ ω with hgdef
  set A : ℝ := ∑ i, |Fh u1 i| + 1 + κ with hAdef
  have hA : 0 < A := by positivity
  set Kn : ℕ → ℕ := fun n => ⌈A * Mrep.size (x n)⌉₊ with hKdef
  have hK : Tendsto Kn atTop atTop :=
    tendsto_nat_ceil_atTop.comp (hsize.const_mul_atTop hA)
  set e : ℕ → ℝ := fun n => b * (C * (Mrep.size (x n))⁻¹ +
    (A + 1) * ∑ i, ((Kn n : ℝ))⁻¹ * g i (Kn n)) with hedef
  have he : Tendsto e atTop (nhds 0) := by
    have e1 : Tendsto (fun n => C * (Mrep.size (x n))⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hsize).const_mul C
    have e2 : Tendsto (fun n => ∑ i, ((Kn n : ℝ))⁻¹ * g i (Kn n)) atTop (nhds 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin I)) (fun i _ => (h638 i).comp hK)
      simp only [Finset.sum_const_zero] at this
      exact this
    simpa using (e1.add (e2.const_mul (A + 1))).const_mul b
  have hFev : ∀ᶠ n in atTop, ∀ i,
      (fam.F (x n) (Mrep.size (x n) * u1) ω i : ℝ) ≤ (|Fh u1 i| + 1) * Mrep.size (x n) := by
    rw [Filter.eventually_all]
    intro i
    have ht1 := fe_uoc_tendsto hF i u1 hu1
    filter_upwards [ht1.eventually (gt_mem_nhds (show Fh u1 i < |Fh u1 i| + 1 by
      linarith [le_abs_self (Fh u1 i)])), hsize.eventually_gt_atTop 0] with n hn hpos
    have := mul_lt_mul_of_pos_left hn hpos
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
    linarith
  have hbig := fe_unscaled_big S (fun n w i => (fam.Zx (x n) w ω i : ℝ))
    (fun n => Mrep.size (x n)) Zh hZ hsize a c δ b ha hδ hwin
  refine fe_lim_bounds (fe_uoc_sum_tendsto hT S u2 (by linarith))
    (fe_uoc_sum_tendsto hT S u1 hu1) he ?_
  filter_upwards [hbig, hFev, hsize.eventually_ge_atTop 1] with n ⟨hspos, hn⟩ hFn hs1
  set sz := Mrep.size (x n) with hsz
  have hcond : ∀ w ∈ Set.Icc (sz * u1) (sz * u2), b < ∑ i ∈ S, (fam.Zx (x n) w ω i : ℝ) :=
    fun w hw => hn u1 u2 h1 h12 h2 w hw
  obtain ⟨hlo, hhi⟩ := hsbp (x n) ω _ _ j (mul_nonneg hspos.le hu1)
    (mul_le_mul_of_nonneg_left h12 hspos.le) hcond
  set M := ⨆ i ∈ poolBuffers dat (dat.p j),
    delayedMax (Mrep.f (x n)).1 (fam.Psi (x n)) v φ i
      (fam.F (x n) (sz * u1) ω i + fam.Nx (x n) (sz * u1) ω i) ω with hMdef
  -- bounds on K
  have hAs : 0 < A * sz := mul_pos hA hspos
  have hKpos : (0 : ℝ) < (Kn n : ℝ) := by
    have := Nat.le_ceil (A * sz); simp only [hKdef]; linarith
  have hKle : (Kn n : ℝ) ≤ (A + 1) * sz := by
    have := Nat.ceil_lt_add_one hAs.le
    simp only [hKdef]; nlinarith
  have hgnn : ∀ i m, 0 ≤ g i m := fun i m => fe_bsup_nonneg _ _
  have hsumg : 0 ≤ ∑ i, g i (Kn n) := Finset.sum_nonneg (fun i _ => hgnn i _)
  have hni : ∀ i, fam.F (x n) (sz * u1) ω i + fam.Nx (x n) (sz * u1) ω i ≤ Kn n := by
    intro i
    have h1' := hFn i
    have h2' : (fam.Nx (x n) (sz * u1) ω i : ℝ) ≤ κ := by exact_mod_cast hκ (x n) (sz * u1) ω i
    have h3 : |Fh u1 i| ≤ ∑ i, |Fh u1 i| :=
      Finset.single_le_sum (f := fun i => |Fh u1 i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h4 : ((fam.F (x n) (sz * u1) ω i + fam.Nx (x n) (sz * u1) ω i : ℕ) : ℝ) ≤ A * sz := by
      push_cast
      have : (κ : ℝ) ≤ κ * sz := by nlinarith [(Nat.cast_nonneg κ : (0:ℝ) ≤ κ)]
      simp only [hAdef]
      nlinarith
    exact_mod_cast h4.trans (Nat.le_ceil _)
  have hMle : M ≤ C + ∑ i, g i (Kn n) := by
    apply Real.iSup_le _ (add_nonneg hC hsumg)
    intro i
    apply Real.iSup_le _ (add_nonneg hC hsumg)
    intro _
    have := fe_dm_le (Mrep.f (x n)).1 (fam.Psi (x n)) v φ i
      (fam.F (x n) (sz * u1) ω i + fam.Nx (x n) (sz * u1) ω i) ω fam.pool
      (fun k hk => fam.Psi_mem_pool (x n) i k hk)
    have hm := fe_bsup_mono (fun ℓ => v i ℓ ω) (hni i)
    have hs := Finset.single_le_sum (f := fun i => g i (Kn n)) (fun i _ => hgnn i _)
      (Finset.mem_univ i)
    simp only [hgdef] at hs ⊢
    linarith
  have hsum2 : ∑ i, g i (Kn n) ≤ sz * ((A + 1) * ∑ i, ((Kn n : ℝ))⁻¹ * g i (Kn n)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hg := hgnn i (Kn n)
    have : 1 ≤ sz * ((A + 1) * (Kn n : ℝ)⁻¹) := by
      rw [← mul_assoc, ← div_eq_mul_inv, le_div_iff₀ hKpos]; nlinarith
    nlinarith
  have hMs : b * M * sz⁻¹ ≤ e n := by
    simp only [hedef]
    rw [mul_assoc, mul_le_mul_iff_of_pos_left hb, mul_inv_le_iff₀ hspos]
    have : C ≤ C * sz⁻¹ * sz := by rw [mul_assoc, inv_mul_cancel₀ hspos.ne', mul_one]
    nlinarith
  have eq : ∑ i ∈ S, sz⁻¹ * fam.T (x n) (sz * u2) ω i -
      ∑ i ∈ S, sz⁻¹ * fam.T (x n) (sz * u1) ω i =
      sz⁻¹ * ∑ i ∈ S, (fam.T (x n) (sz * u2) ω i - fam.T (x n) (sz * u1) ω i) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, ← Finset.sum_sub_distrib]
  try simp only
  rw [eq]
  have hinv : 0 < sz⁻¹ := inv_pos.mpr hspos
  constructor
  · have := mul_le_mul_of_nonneg_left hlo hinv.le
    have e1 : sz⁻¹ * ((sz * u2 - sz * u1) * b - b * M) = (u2 - u1) * b - b * M * sz⁻¹ := by
      field_simp
    linarith
  · have := mul_le_mul_of_nonneg_left hhi hinv.le
    have e1 : sz⁻¹ * ((sz * u2 - sz * u1) * b) = (u2 - u1) * b := by field_simp
    linarith

theorem sbp_main
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ)
    (σ : Equiv.Perm (Fin I)) (hsbp : SBPNonPreemptive dat σ fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
    (h638 : ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v i ℓ ω) atTop (nhds 0))
    (hDcont : Continuous Dh) (hFcont : Continuous Fh) (hTcont : Continuous Th)
    (hZcont : Continuous Zh) (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hD : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.D (x n) (Mrep.size (x n) * t) ω i : ℝ)) Dh)
    (hF : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω i : ℝ)) Fh)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh)
    (j : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ Hset dat σ j, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ Hset dat σ j, Th s i) (dat.b (dat.p j)) t :=
  sbp_core dat fam σ hsbp ω x Fh Th Zh h638 hZcont hsize hF hT hZ j t ht hz

end ProcessingNetworks.FluidEquations

open ProcessingNetworks.FluidEquations
open MeasureTheory Filter ProcessingNetworks.Stability

theorem solution
    {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I K : ℕ}
    {N : ℝ → Ω → Fin I → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I I N Z} (dat : QueueingNetworkData I K)
    {E : Fin I → ℝ → Ω → ℕ} {v : Fin I → ℕ → Ω → ℝ} {φ : Fin I → ℕ → Ω → Fin I → ℕ}
    (fam : ProcessFamily Mrep dat.toSPNData E v φ)
    (σ : Equiv.Perm (Fin I)) (hsbp : SBPNonPreemptive dat σ fam)
    (ω : Ω) (x : ℕ → Xstate) (Dh Fh Th Zh : ℝ → Fin I → ℝ)
    (h638 : ∀ i, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ⨆ ℓ ∈ Finset.range n, v i ℓ ω) atTop (nhds 0))
    (hDcont : Continuous Dh) (hFcont : Continuous Fh) (hTcont : Continuous Th)
    (hZcont : Continuous Zh) (hsize : Tendsto (fun n => Mrep.size (x n)) atTop atTop)
    (hD : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.D (x n) (Mrep.size (x n) * t) ω i : ℝ)) Dh)
    (hF : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.F (x n) (Mrep.size (x n) * t) ω i : ℝ)) Fh)
    (hT : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * fam.T (x n) (Mrep.size (x n) * t) ω i) Th)
    (hZ : UOCConverges
      (fun n t i => (Mrep.size (x n))⁻¹ * (fam.Zx (x n) (Mrep.size (x n) * t) ω i : ℝ)) Zh)
    (j : Fin I) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ Hset dat σ j, Zh t i) :
    HasDerivAt (fun s => ∑ i ∈ Hset dat σ j, Th s i) (dat.b (dat.p j)) t := by
  exact sbp_main dat fam σ hsbp ω x Dh Fh Th Zh h638 hDcont hFcont hTcont hZcont hsize hD hF hT hZ j t ht hz
