-- Prove2me | solution 1 for RockafellarMaxMono.Cyclic.maximal_cyclically_monotone_iff_subdiff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T03:33:00.321225+00:00
-- url     : https://prove2.me/submissions/23d86335-ed0d-406b-b7dd-748579bde0b9

import Definitions.Def_RockafellarMaxMono_Cyclic_CyclicallyMonotone
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Mathlib
set_option autoImplicit false
section



namespace RockafellarMaxMono.Maximality

/-- Rockafellar (1970), p. 209: a multivalued mapping `T : V → V*` (encoded as
`V → Set (StrongDual ℝ V)`) is a *monotone operator* if
`⟨x₀ − x₁, x₀* − x₁*⟩ ≥ 0` whenever `x₀* ∈ T(x₀)` and `x₁* ∈ T(x₁)`. -/
def IsMonotoneOp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  ∀ (x₀ x₁ : V) (x₀' x₁' : StrongDual ℝ V), x₀' ∈ T x₀ → x₁' ∈ T x₁ →
    0 ≤ (x₀' - x₁') (x₀ - x₁)

/-- Rockafellar (1970), p. 209: a monotone operator `T : V → V*` is *maximal monotone* if its
graph `G(T) = {(x, x*) | x* ∈ T(x)}` is not properly contained in the graph of any other
monotone operator `T' : V → V*`; equivalently, every monotone `T'` whose graph contains the
graph of `T` coincides with `T`. -/
def IsMaximalMonotone {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → Set (StrongDual ℝ V)) : Prop :=
  IsMonotoneOp T ∧
    ∀ T' : V → Set (StrongDual ℝ V), IsMonotoneOp T' → (∀ x, T x ⊆ T' x) → ∀ x, T' x = T x

end RockafellarMaxMono.Maximality

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
theorem bregman_existence_accepted_subdiff_maximal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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


end

section

section
set_option autoImplicit false


namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), (2.1), p. 210: the *conjugate* of `f : V → (−∞, +∞]` is the function
on the dual `V* = StrongDual ℝ V` given by `f*(x*) = sup {⟨x, x*⟩ − f(x) | x ∈ V}`,
computed in `EReal` (so `f*` may take the value `+∞`). The biconjugate `f**` is
`conj (conj f)`, a function on the bidual `StrongDual ℝ (StrongDual ℝ V)`. -/
noncomputable def conj {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : V → EReal) :
    StrongDual ℝ V → EReal :=
  fun x' => ⨆ x : V, ((x' x : ℝ) : EReal) - f x

end RockafellarMaxMono.Shared


namespace RockafellarMaxMono.Shared

/-- Rockafellar (1970), p. 213: the continuous convex function `j(x) = (1/2)‖x‖²`,
regarded as a (finite-valued) function `V → (−∞, +∞]`. -/
noncomputable def halfSqNorm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) :
    EReal :=
  ((‖x‖ ^ 2 / 2 : ℝ) : EReal)

end RockafellarMaxMono.Shared

section

open Filter Topology Set

namespace RockafellarMaxMono.Cyclic.AcceptedFinite

section Core
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def rqq (h : V → ℝ) (x u : V) (t : ℝ) : ℝ := (h (x + t • u) - h x) / t

lemma rqq_mono (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) : rqq h x u s ≤ rqq h x u t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have key : h (x + s • u) ≤ (1 - s / t) * h x + (s / t) * h (x + t • u) := by
    have e : x + s • u = (1 - s / t) • x + (s / t) • (x + t • u) := by
      rw [smul_add, smul_smul, div_mul_cancel₀ _ ht.ne']
      rw [sub_smul, one_smul]; abel
    rw [e]
    have := hconv.2 (Set.mem_univ x) (Set.mem_univ (x + t • u))
      (sub_nonneg.2 ((div_le_one ht).2 hst)) (div_nonneg hs.le ht.le) (by ring)
    simpa [smul_eq_mul] using this
  unfold rqq
  rw [div_le_div_iff₀ hs ht]
  have h1 : (s / t) * t = s := div_mul_cancel₀ _ ht.ne'
  have h2 : (h (x + s • u) - h x) ≤ (s / t) * (h (x + t • u) - h x) := by linarith
  have h3 : (h (x + s • u) - h x) * t ≤ (s / t) * (h (x + t • u) - h x) * t :=
    mul_le_mul_of_nonneg_right h2 ht.le
  calc (h (x + s • u) - h x) * t ≤ (s / t) * (h (x + t • u) - h x) * t := h3
    _ = (h (x + t • u) - h x) * s := by rw [mul_comm (s/t), mul_assoc, h1]

lemma rqq_lb (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {t : ℝ} (ht : 0 < t) :
    h x - h (x - u) ≤ rqq h x u t := by
  have h1t : 0 < 1 + t := by linarith
  have key : h x ≤ (t / (1 + t)) * h (x - u) + (1 / (1 + t)) * h (x + t • u) := by
    have e : x = (t / (1 + t)) • (x - u) + (1 / (1 + t)) • (x + t • u) := by
      have hab : t / (1 + t) + 1 / (1 + t) = 1 := by
        rw [← add_div, div_eq_one_iff_eq h1t.ne']; ring
      have h2 : 1 / (1 + t) * t - t / (1 + t) = 0 := by ring
      calc x = (t / (1 + t) + 1 / (1 + t)) • x + (1 / (1 + t) * t - t / (1 + t)) • u := by
            rw [hab, h2]; simp
        _ = _ := by module
    conv_lhs => rw [e]
    have := hconv.2 (Set.mem_univ (x - u)) (Set.mem_univ (x + t • u))
      (div_nonneg ht.le h1t.le) (div_nonneg zero_le_one h1t.le) (by field_simp; ring)
    simpa [smul_eq_mul] using this
  unfold rqq
  rw [le_div_iff₀ ht]
  have : (1 + t) * h x ≤ t * h (x - u) + h (x + t • u) := by
    have := mul_le_mul_of_nonneg_left key h1t.le
    have e1 : (1 + t) * ((t / (1 + t)) * h (x - u) + (1 / (1 + t)) * h (x + t • u))
        = t * h (x - u) + h (x + t • u) := by field_simp
    linarith
  nlinarith

noncomputable def rpp (h : V → ℝ) (x u : V) : ℝ := sInf (rqq h x u '' Ioi 0)

lemma rpp_bdd (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) :
    BddBelow (rqq h x u '' Ioi 0) := by
  refine ⟨h x - h (x - u), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact rqq_lb h hconv x u ht

lemma rpp_le (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {t : ℝ} (ht : 0 < t) :
    rpp h x u ≤ rqq h x u t :=
  csInf_le (rpp_bdd h hconv x u) ⟨t, ht, rfl⟩

lemma le_rpp (h : V → ℝ) (x u : V) {c : ℝ} (hc : ∀ t, 0 < t → c ≤ rqq h x u t) :
    c ≤ rpp h x u := by
  apply le_csInf ((Set.nonempty_Ioi (a := (0:ℝ))).image _)
  rintro _ ⟨t, ht, rfl⟩
  exact hc t ht

lemma rqq_smul (h : V → ℝ) (x u : V) {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    rqq h x (c • u) t = c * rqq h x u (t * c) := by
  unfold rqq
  rw [smul_smul]
  field_simp

lemma rpp_hom (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u : V) {c : ℝ} (hc : 0 < c) :
    rpp h x (c • u) = c * rpp h x u := by
  apply le_antisymm
  · have : rpp h x (c • u) / c ≤ rpp h x u := by
      apply le_rpp
      intro t ht
      rw [div_le_iff₀ hc]
      have := rpp_le h hconv x (c • u) (t := t / c) (div_pos ht hc)
      rw [rqq_smul h x u hc (div_pos ht hc), div_mul_cancel₀ _ hc.ne'] at this
      linarith
    rw [div_le_iff₀ hc] at this; linarith
  · apply le_rpp
    intro t ht
    rw [rqq_smul h x u hc ht]
    exact mul_le_mul_of_nonneg_left (rpp_le h hconv x u (mul_pos ht hc)) hc.le

lemma rqq_add (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u v : V) {t : ℝ} (ht : 0 < t) :
    rqq h x (u + v) t ≤ rqq h x u (2 * t) + rqq h x v (2 * t) := by
  have key : h (x + t • (u + v)) ≤ (1/2 : ℝ) * h (x + (2 * t) • u) + (1/2 : ℝ) * h (x + (2*t) • v) := by
    have e : x + t • (u + v) = (1/2 : ℝ) • (x + (2 * t) • u) + (1/2 : ℝ) • (x + (2*t) • v) := by
      module
    rw [e]
    have := hconv.2 (Set.mem_univ (x + (2 * t) • u)) (Set.mem_univ (x + (2*t) • v))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    simpa [smul_eq_mul] using this
  unfold rqq
  rw [← add_div, div_le_div_iff₀ ht (by linarith)]
  nlinarith

lemma rpp_add (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x u v : V) :
    rpp h x (u + v) ≤ rpp h x u + rpp h x v := by
  have H : ∀ s s' : ℝ, 0 < s → 0 < s' → rpp h x (u + v) ≤ rqq h x u s + rqq h x v s' := by
    intro s s' hs hs'
    have hm : 0 < min s s' := lt_min hs hs'
    have a1 := rqq_mono h hconv x u hm (min_le_left s s')
    have a2 := rqq_mono h hconv x v hm (min_le_right s s')
    have a3 := rqq_add h hconv x u v (t := min s s' / 2) (by linarith)
    have a4 := rpp_le h hconv x (u + v) (t := min s s' / 2) (by linarith)
    have : 2 * (min s s' / 2) = min s s' := by ring
    rw [this] at a3
    linarith
  have H2 : ∀ s', 0 < s' → rpp h x (u + v) - rqq h x v s' ≤ rpp h x u := by
    intro s' hs'
    apply le_rpp; intro s hs; have := H s s' hs hs'; linarith
  have : rpp h x (u + v) - rpp h x u ≤ rpp h x v := by
    apply le_rpp; intro s' hs'; have := H2 s' hs'; linarith
  linarith

lemma rpp_zero (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (x : V) : rpp h x 0 = 0 := by
  have : rqq h x 0 '' Ioi 0 = {0} := by
    ext y; simp only [mem_image, mem_Ioi, mem_singleton_iff, rqq, smul_zero, add_zero, sub_self,
      zero_div]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · rintro rfl; exact ⟨1, one_pos, rfl⟩
  unfold rpp; rw [this, csInf_singleton]

lemma exists_sub (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (x u : V) :
    ∃ g : StrongDual ℝ V, (∀ y, h x + g (y - x) ≤ h y) ∧ g u = rpp h x u := by
  set f : V →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' u (rpp h x u) (fun c hc => by
    rcases smul_eq_zero.1 hc with hc | hc
    · simp [hc]
    · subst hc; simp [rpp_zero h hconv x]) with hfdef
  have hf : ∀ z : f.domain, f z ≤ rpp h x z := by
    rintro ⟨z, hz⟩
    have hz' := hz
    rw [hfdef, LinearPMap.domain_mkSpanSingleton, Submodule.mem_span_singleton] at hz'
    obtain ⟨c, rfl⟩ := hz'
    have hfa : f ⟨c • u, hz⟩ = c * rpp h x u := LinearPMap.mkSpanSingleton'_apply _ _ _ c hz
    rw [hfa]
    show c * rpp h x u ≤ rpp h x (c • u)
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have e : c • u = (-c) • (-u) := by rw [neg_smul_neg]
      rw [e, rpp_hom h hconv x _ (neg_pos.2 hc)]
      have := rpp_add h hconv x u (-u)
      rw [add_neg_cancel, rpp_zero h hconv x] at this
      nlinarith
    · subst hc; simp [rpp_zero h hconv x]
    · rw [rpp_hom h hconv x _ hc]
  obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear f (rpp h x)
    (fun c hc v => rpp_hom h hconv x v hc) (rpp_add h hconv x) hf
  have hgq : ∀ v, g v ≤ h (x + v) - h x := by
    intro v
    have := (hg2 v).trans (rpp_le h hconv x v one_pos)
    simpa [rqq] using this
  -- continuity
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := x)) 1 one_pos
  have hb : ∀ v : V, ‖v‖ ≤ δ / 2 → g v ≤ 1 := by
    intro v hv
    have := hδh (x := x + v) (by rw [dist_eq_norm]; simp; linarith)
    rw [Real.dist_eq] at this
    have := hgq v
    have := (abs_lt.1 ‹|h (x + v) - h x| < 1›).2
    linarith
  have hδ2 : 0 < δ / 2 := by linarith
  have bound : ∀ v : V, ‖g v‖ ≤ (2 / δ) * ‖v‖ := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    set w := ((δ / 2) / ‖v‖) • v with hw
    have hwn : ‖w‖ ≤ δ / 2 := by
      rw [hw, norm_smul, Real.norm_of_nonneg (div_nonneg hδ2.le hn.le), div_mul_cancel₀ _ hn.ne']
    have hwn' : ‖-w‖ ≤ δ / 2 := by rwa [norm_neg]
    have a1 := hb w hwn
    have a2 := hb (-w) hwn'
    rw [map_neg] at a2
    rw [hw, map_smul, smul_eq_mul] at a1 a2
    rw [Real.norm_eq_abs, abs_le]
    have e : (2 / δ) * ‖v‖ = 1 / ((δ / 2) / ‖v‖) := by field_simp
    have hpos : 0 < (δ / 2) / ‖v‖ := div_pos hδ2 hn
    rw [e]
    constructor
    · have : -1 ≤ (δ / 2 / ‖v‖) * g v := by linarith
      calc -(1 / (δ / 2 / ‖v‖)) = (1 / (δ / 2 / ‖v‖)) * (-1) := by ring
        _ ≤ (1 / (δ / 2 / ‖v‖)) * ((δ / 2 / ‖v‖) * g v) := by gcongr
        _ = g v := by field_simp
    · rw [le_div_iff₀ hpos]; linarith
  refine ⟨g.mkContinuous (2 / δ) bound, ?_, ?_⟩
  · intro y
    rw [LinearMap.mkContinuous_apply]
    have := hgq (y - x)
    rw [add_sub_cancel] at this
    linarith
  · rw [LinearMap.mkContinuous_apply]
    have := hg1 ⟨u, Submodule.mem_span_singleton_self u⟩
    have hfa1 : f ⟨u, Submodule.mem_span_singleton_self u⟩ = rpp h x u :=
      LinearPMap.mkSpanSingleton'_apply_self _ _ _ _
    rw [this, hfa1]


lemma memiff (φ : V → ℝ) (x' : StrongDual ℝ V) (y : V) :
    x' ∈ Shared.subdiff (fun z => ((φ z : ℝ) : EReal)) y ↔ ∀ z, φ y + x' (z - y) ≤ φ z := by
  simp only [Shared.subdiff, Set.mem_setOf_eq, ← EReal.coe_add, EReal.coe_le_coe_iff]

lemma sub_le_rpp (h : V → ℝ) (x u : V) (x' : StrongDual ℝ V)
    (hx' : ∀ z, h x + x' (z - x) ≤ h z) : x' u ≤ rpp h x u := by
  apply le_rpp
  intro t ht
  have := hx' (x + t • u)
  rw [add_sub_cancel_left, map_smul, smul_eq_mul] at this
  unfold rqq
  rw [le_div_iff₀ ht]; linarith

lemma sub_norm_bound (h : V → ℝ) (hcont : Continuous h) (x : V) :
    ∃ C : ℝ, ∀ x' : StrongDual ℝ V, (∀ z, h x + x' (z - x) ≤ h z) → ‖x'‖ ≤ C := by
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuousAt_iff.1 (hcont.continuousAt (x := x)) 1 one_pos
  have hδ2 : 0 < δ / 2 := by linarith
  refine ⟨2 / δ, fun x' hx' => ?_⟩
  have hb : ∀ v : V, ‖v‖ ≤ δ / 2 → x' v ≤ 1 := by
    intro v hv
    have := hδh (x := x + v) (by rw [dist_eq_norm]; simp; linarith)
    rw [Real.dist_eq] at this
    have h2 := hx' (x + v)
    rw [add_sub_cancel_left] at h2
    have := (abs_lt.1 this).2
    linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w := ((δ / 2) / ‖v‖) • v with hw
  have hwn : ‖w‖ ≤ δ / 2 := by
    rw [hw, norm_smul, Real.norm_of_nonneg (div_nonneg hδ2.le hn.le), div_mul_cancel₀ _ hn.ne']
  have hwn' : ‖-w‖ ≤ δ / 2 := by rwa [norm_neg]
  have a1 := hb w hwn
  have a2 := hb (-w) hwn'
  rw [map_neg] at a2
  rw [hw, map_smul, smul_eq_mul] at a1 a2
  rw [Real.norm_eq_abs, abs_le]
  have e : (2 / δ) * ‖v‖ = 1 / ((δ / 2) / ‖v‖) := by field_simp
  have hpos : 0 < (δ / 2) / ‖v‖ := div_pos hδ2 hn
  rw [e]
  constructor
  · have : -1 ≤ (δ / 2 / ‖v‖) * x' v := by linarith
    calc -(1 / (δ / 2 / ‖v‖)) = (1 / (δ / 2 / ‖v‖)) * (-1) := by ring
      _ ≤ (1 / (δ / 2 / ‖v‖)) * ((δ / 2 / ‖v‖) * x' v) := by gcongr
      _ = x' v := by field_simp
  · rw [le_div_iff₀ hpos]; linarith

theorem dirDeriv_core (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (x : V) :
    (Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x).Nonempty ∧
    IsCompact (StrongDual.toWeakDual '' Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) ∧
    ∀ u : V, ∃ d : ℝ,
      Tendsto (fun t : ℝ => (h (x + t • u) - h x) / t) (𝓝[>] 0) (𝓝 d) ∧
      IsGreatest ((fun x' : StrongDual ℝ V => x' u) ''
        Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) d := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨g, hg, -⟩ := exists_sub h hconv hcont x 0
    exact ⟨g, (memiff h g x).2 hg⟩
  · obtain ⟨C, hC⟩ := sub_norm_bound h hcont x
    apply WeakDual.isCompact_of_bounded_of_closed
    · rw [← WeakDual.isBounded_toWeakDual_preimage_iff_isBounded]
      apply (Metric.isBounded_closedBall (x := (0 : StrongDual ℝ V)) (r := C)).subset
      rintro w ⟨x', hx', hw⟩
      have : x' = w := hw
      subst this
      simpa using hC x' ((memiff h x' x).1 hx')
    · have e : StrongDual.toWeakDual '' Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x =
          ⋂ y : V, {w : WeakDual ℝ V | h x + w (y - x) ≤ h y} := by
        ext w
        simp only [Set.mem_image, Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x', hx', rfl⟩ y
          exact (memiff h x' x).1 hx' y
        · intro hw
          exact ⟨WeakDual.toStrongDual w, (memiff h _ x).2 hw, rfl⟩
      rw [e]
      exact isClosed_iInter fun y =>
        isClosed_le (continuous_const.add (WeakDual.eval_continuous _)) continuous_const
  · intro u
    obtain ⟨g, hg, hgu⟩ := exists_sub h hconv hcont x u
    refine ⟨rpp h x u, ?_, ⟨⟨g, (memiff h g x).2 hg, hgu⟩, ?_⟩⟩
    · rw [tendsto_order]
      constructor
      · intro a' ha'
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact lt_of_lt_of_le ha' (rpp_le h hconv x u ht)
      · intro b' hb'
        obtain ⟨_, ⟨t0, ht0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
          ((Set.nonempty_Ioi (a := (0:ℝ))).image _) hb'
        filter_upwards [Ioo_mem_nhdsGT ht0] with t ht
        exact lt_of_le_of_lt (rqq_mono h hconv x u ht.1 ht.2.le) hlt
    · rintro _ ⟨x', hx', rfl⟩
      exact sub_le_rpp h x u x' ((memiff h x' x).1 hx')

lemma mono_line (h k : V → ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h) (kcont : Continuous k)
    (hsub : ∀ x : V, Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x ⊆
      Shared.subdiff (fun y => ((k y : ℝ) : EReal)) x) (a d : V) :
    k a - h a ≤ k (a + d) - h (a + d) := by
  set g : ℝ → ℝ := fun t => k (a + t • d) - h (a + t • d) with hgdef
  have gc : Continuous g := by
    have c1 : Continuous fun t : ℝ => a + t • d := continuous_const.add (continuous_id.smul continuous_const)
    exact (kcont.comp c1).sub (hcont.comp c1)
  have key : ∀ ε : ℝ, 0 < ε → g 0 ≤ g 1 + ε := by
    intro ε hε
    have := image_le_of_liminf_slope_right_lt_deriv_boundary' (f := fun t => - g t) (f' := fun _ => 0)
      (a := 0) (b := 1) gc.neg.continuousOn ?_ (B := fun t => -g 0 + ε * t) (B' := fun _ => ε)
      (by simp) (by fun_prop) ?_ (fun _ _ _ => hε) (x := 1) ⟨zero_le_one, le_rfl⟩
    · have h2 : -g 1 ≤ -g 0 + ε * 1 := this
      linarith
    · intro t _ r hr
      apply Filter.Eventually.frequently
      set y := a + t • d with hy
      obtain ⟨x', hx', hx'd⟩ := exists_sub h hconv hcont y d
      have hk := (memiff k x' y).1 (hsub y ((memiff h x' y).2 hx'))
      obtain ⟨_, ⟨t0, ht0, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
          ((Set.nonempty_Ioi (a := (0:ℝ))).image _) (show rpp h y d < rpp h y d + r by linarith)
      have ht0' : t < t + t0 := by linarith [Set.mem_Ioi.1 ht0]
      filter_upwards [Ioo_mem_nhdsGT ht0'] with z hz
      have hzt : 0 < z - t := by linarith [hz.1]
      have e : a + z • d = y + (z - t) • d := by rw [hy, sub_smul]; abel
      have q1 := rqq_mono h hconv y d (t := t0) hzt (by linarith [hz.2])
      have hk2 := hk (y + (z - t) • d)
      rw [add_sub_cancel_left, map_smul, smul_eq_mul] at hk2
      unfold rqq at q1
      rw [div_le_iff₀ hzt] at q1
      rw [slope_def_field]
      simp only [hgdef, e]
      rw [← hy, div_lt_iff₀ hzt]
      have : rqq h y d t0 * (z - t) < (rpp h y d + r) * (z - t) := mul_lt_mul_of_pos_right hlt hzt
      rw [← hx'd] at this
      unfold rqq at this
      nlinarith
    · intro t _
      have := ((hasDerivAt_id t).const_mul ε).const_add (-g 0)
      simpa using this.hasDerivWithinAt
  have h1 : g 0 ≤ g 1 := le_of_forall_pos_le_add key
  simpa [hgdef] using h1

theorem finite_core {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (h k : V → ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (kconv : ConvexOn ℝ Set.univ k) (kcont : Continuous k)
    (hsub : ∀ x : V, Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x ⊆
      Shared.subdiff (fun y => ((k y : ℝ) : EReal)) x) :
    ∃ c : ℝ, ∀ x : V, k x = h x + c := by
  refine ⟨k 0 - h 0, fun x => ?_⟩
  have a1 := mono_line h k hconv hcont kcont hsub 0 x
  have a2 := mono_line h k hconv hcont kcont hsub x (-x)
  simp only [zero_add, add_neg_cancel] at a1 a2
  linarith

end Core
end RockafellarMaxMono.Cyclic.AcceptedFinite

open RockafellarMaxMono.Cyclic.AcceptedFinite
open RockafellarMaxMono

theorem uniqueness_accepted_finite {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (h k : V → ℝ)
    (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (kconv : ConvexOn ℝ Set.univ k) (kcont : Continuous k)
    (hsub : ∀ x : V, Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x ⊆
      Shared.subdiff (fun y => ((k y : ℝ) : EReal)) x) :
    ∃ c : ℝ, ∀ x : V, k x = h x + c := by
  exact finite_core h k hconv hcont kconv kcont hsub
end

section
open Pointwise


namespace RockafellarMaxMono.Cyclic.AcceptedSumRule

section SumRule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma sr_convexB (x : E) :
    Convex ℝ {p : E × ℝ | p.2 < ‖x‖ ^ 2 / 2 - ‖p.1‖ ^ 2 / 2} := by
  intro p hp q hq s t hs ht hst
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hp hq ⊢
  have hn : ‖s • p.1 + t • q.1‖ ≤ s * ‖p.1‖ + t * ‖q.1‖ := by
    calc ‖s • p.1 + t • q.1‖ ≤ ‖s • p.1‖ + ‖t • q.1‖ := norm_add_le _ _
      _ = s * ‖p.1‖ + t * ‖q.1‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
  have h0 : 0 ≤ ‖s • p.1 + t • q.1‖ := norm_nonneg _
  have hsq : ‖s • p.1 + t • q.1‖ ^ 2 ≤ (s * ‖p.1‖ + t * ‖q.1‖) ^ 2 := by
    exact pow_le_pow_left₀ h0 hn 2
  have hconvx : (s * ‖p.1‖ + t * ‖q.1‖) ^ 2 ≤ s * ‖p.1‖ ^ 2 + t * ‖q.1‖ ^ 2 := by
    have : t = 1 - s := by linarith
    subst this
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (‖p.1‖ - ‖q.1‖))]
  have := mul_le_mul_of_nonneg_left hp.le hs
  have := mul_le_mul_of_nonneg_left hq.le ht
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · subst hs0
    have : t = 1 := by linarith
    subst this
    simp only [zero_mul, zero_add, one_mul, zero_smul, one_smul] at *
    exact hq
  · have := mul_lt_mul_of_pos_left hp hs0
    nlinarith

theorem sumrule_core (f : E → EReal) (hf : Shared.ProperConvex f) :
    ∀ x : E, Shared.subdiff (fun y => f y + Shared.halfSqNorm y) x =
      Shared.subdiff f x + Shared.subdiff Shared.halfSqNorm x := by
  intro x
  apply Set.Subset.antisymm
  · intro xs hxs
    simp only [Shared.subdiff, Set.mem_setOf_eq, Shared.halfSqNorm] at hxs
    -- f x finite
    have hfx : f x ≠ ⊤ := by
      intro htop
      obtain ⟨y0, hy0⟩ := hf.2.1
      have := hxs y0
      rw [htop, EReal.top_add_coe, EReal.top_add_coe, top_le_iff] at this
      have h2 : f y0 + ((‖y0‖ ^ 2 / 2 : ℝ) : EReal) ≠ ⊤ := by
        lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c
        rw [← EReal.coe_add]; exact EReal.coe_ne_top _
      exact h2 this
    lift f x to ℝ using ⟨hfx, hf.1 x⟩ with a ha
    set J : E → ℝ := fun y => ‖y‖ ^ 2 / 2 with hJ
    have hreal : ∀ y (c : ℝ), f y = c → a + J x + xs (y - x) ≤ c + J y := by
      intro y c hc
      have := hxs y
      rw [hc, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
        at this
      exact this
    set A : Set (E × ℝ) := {p | ∃ c : ℝ, f p.1 = c ∧ c - a - xs (p.1 - x) ≤ p.2} with hA
    set B : Set (E × ℝ) := {p : E × ℝ | p.2 < ‖x‖ ^ 2 / 2 - ‖p.1‖ ^ 2 / 2} with hB
    have hBo : IsOpen B := isOpen_lt continuous_snd (continuous_const.sub
      (((continuous_norm.comp continuous_fst).pow 2).div_const 2))
    have hAc : Convex ℝ A := by
      rintro ⟨y1, r1⟩ ⟨c1, hc1, hr1⟩ ⟨y2, r2⟩ ⟨c2, hc2, hr2⟩ s t hs ht hst
      simp only at hc1 hr1 hc2 hr2
      rcases eq_or_lt_of_le ht with ht0 | ht0
      · subst ht0
        have : s = 1 := by linarith
        subst this
        exact ⟨c1, by simpa using hc1, by simpa using hr1⟩
      rcases eq_or_lt_of_le hs with hs0 | hs0
      · subst hs0
        have : t = 1 := by linarith
        subst this
        exact ⟨c2, by simpa using hc2, by simpa using hr2⟩
      have hts : s = 1 - t := by linarith
      subst hts
      have hcv := hf.2.2 y1 y2 t ht0 (by linarith)
      rw [hc1, hc2, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hcv
      have hne : f ((1 - t) • y1 + t • y2) ≠ ⊤ :=
        ne_top_of_le_ne_top (EReal.coe_ne_top _) hcv
      lift f ((1 - t) • y1 + t • y2) to ℝ using ⟨hne, hf.1 _⟩ with c hcdef
      rw [EReal.coe_le_coe_iff] at hcv
      refine ⟨c, ?_, ?_⟩
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; exact hcdef.symm
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, map_sub, map_add, map_smul]
        simp only [map_sub] at hr1 hr2
        nlinarith
    have hdisj : Disjoint B A := by
      rw [Set.disjoint_left]
      rintro ⟨y, r⟩ hb ⟨c, hc, hr⟩
      simp only [hB, Set.mem_setOf_eq] at hb hc hr
      have := hreal y c hc
      simp only [hJ] at this
      linarith
    obtain ⟨ℓ, u, hℓB, hℓA⟩ := geometric_hahn_banach_open (sr_convexB x) hBo hAc hdisj
    set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
    set β : ℝ := ℓ (0, 1) with hβ
    have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
      intro y r
      have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
      rw [this, map_add, map_smul, smul_eq_mul]
      rfl
    have hxA : (x, (0:ℝ)) ∈ A := ⟨a, ha.symm, by simp⟩
    have hu1 : u ≤ φ x := by have := hℓA _ hxA; rwa [hℓ, zero_mul, add_zero] at this
    have hxB : ∀ r : ℝ, r < 0 → φ x + r * β < u := by
      intro r hr
      have := hℓB (x, r) (by simp [hB]; exact hr)
      rwa [hℓ] at this
    have hβpos : 0 < β := by
      have := hxB (-1) (by norm_num)
      linarith
    have hu2 : u = φ x := by
      by_contra hne
      have hlt : u < φ x := lt_of_le_of_ne hu1 hne
      have := hxB ((u - φ x) / β) (div_neg_of_neg_of_pos (by linarith) hβpos)
      rw [div_mul_cancel₀ _ hβpos.ne'] at this
      linarith
    set x2 : StrongDual ℝ E := β⁻¹ • φ with hx2
    refine ⟨xs - x2, ?_, x2, ?_, by simp⟩
    · simp only [Shared.subdiff, Set.mem_setOf_eq]
      intro y
      rcases eq_or_ne (f y) ⊤ with hy | hy
      · rw [hy]; exact le_top
      lift f y to ℝ using ⟨hy, hf.1 y⟩ with c hc
      rw [← ha, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hmem : (y, c - a - xs (y - x)) ∈ A := ⟨c, hc.symm, le_rfl⟩
      have := hℓA _ hmem
      rw [hℓ] at this
      simp only [hx2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        map_sub]
      simp only [map_sub] at this
      rw [hu2] at this
      have e : β⁻¹ * (φ y - φ x) * β = φ y - φ x := by field_simp
      nlinarith
    · simp only [Shared.subdiff, Set.mem_setOf_eq, Shared.halfSqNorm]
      intro y
      rw [← EReal.coe_add, EReal.coe_le_coe_iff]
      simp only [hx2, ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub]
      have key : φ y + (‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2) * β ≤ φ x := by
        by_contra hcon
        push_neg at hcon
        have := hℓB (y, (φ x - φ y) / β) (by
          simp only [hB, Set.mem_setOf_eq]
          rw [div_lt_iff₀ hβpos]; linarith)
        rw [hℓ, div_mul_cancel₀ _ hβpos.ne'] at this
        linarith
      rw [← sub_nonneg] at key ⊢
      have e : ‖y‖ ^ 2 / 2 - (‖x‖ ^ 2 / 2 + (β⁻¹ * φ y - β⁻¹ * φ x))
          = β⁻¹ * (φ x - (φ y + (‖x‖ ^ 2 / 2 - ‖y‖ ^ 2 / 2) * β)) := by field_simp; ring
      rw [e]; exact mul_nonneg (inv_nonneg.2 hβpos.le) key
  · rintro _ ⟨x1, hx1, x2, hx2, rfl⟩
    simp only [Shared.subdiff, Set.mem_setOf_eq] at hx1 hx2 ⊢
    intro y
    rw [ContinuousLinearMap.add_apply, EReal.coe_add]
    calc f x + Shared.halfSqNorm x + (((x1 (y - x) : ℝ) : EReal) + ((x2 (y - x) : ℝ) : EReal))
        = (f x + ((x1 (y - x) : ℝ) : EReal)) + (Shared.halfSqNorm x + ((x2 (y - x) : ℝ) : EReal)) :=
          add_add_add_comm _ _ _ _
      _ ≤ f y + Shared.halfSqNorm y := add_le_add (hx1 y) (hx2 y)

end SumRule
end RockafellarMaxMono.Cyclic.AcceptedSumRule

open RockafellarMaxMono.Cyclic.AcceptedSumRule
open RockafellarMaxMono

theorem uniqueness_accepted_sumrule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.subdiff (fun y => f y + Shared.halfSqNorm y) x = Shared.subdiff f x + Shared.subdiff Shared.halfSqNorm x := by
  exact sumrule_core f hf
end

section



namespace RockafellarMaxMono.Cyclic.AcceptedConjFin

section ConjFin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cf_minorant (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∃ (l : StrongDual ℝ E) (b : ℝ), ∀ y (c : ℝ), f y = c → l y + b ≤ c := by
  set C : Set (E × ℝ) := {p | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hC
  have hCc : IsClosed C := by
    have : C = (Prod.map id (fun r : ℝ => (r : EReal))) ⁻¹' {p : E × EReal | f p.1 ≤ p.2} := by
      ext p; simp [hC]
    rw [this]
    exact hlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  have hCv : Convex ℝ C := by
    rintro ⟨y1, r1⟩ h1 ⟨y2, r2⟩ h2 s t hs ht hst
    simp only [hC, Set.mem_setOf_eq] at h1 h2 ⊢
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      simpa using h1
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · subst hs0
      have : t = 1 := by linarith
      subst this
      simpa using h2
    have hts : s = 1 - t := by linarith
    subst hts
    have hne1 : f y1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hne2 : f y2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hcv := hf.2.2 y1 y2 t ht0 (by linarith)
    lift f y1 to ℝ using ⟨hne1, hf.1 y1⟩ with c1
    lift f y2 to ℝ using ⟨hne2, hf.1 y2⟩ with c2
    rw [EReal.coe_le_coe_iff] at h1 h2
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hcv
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine hcv.trans ?_
    rw [EReal.coe_le_coe_iff]
    nlinarith
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hnot : (y0, c0 - 1) ∉ C := by
    simp only [hC, Set.mem_setOf_eq, ← hc0, EReal.coe_le_coe_iff, not_le]; linarith
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hCv hCc hnot
  set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set β : ℝ := ℓ (0, 1) with hβ
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have h0 := hl2 (y0, c0) (by simp [hC, ← hc0])
  rw [hℓ] at hl1 h0
  have hβ : 0 < β := by nlinarith
  refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_⟩
  have := hl2 (y, c) (by simp [hC, hc])
  rw [hℓ] at this
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
  have e : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  have hi : 0 < β⁻¹ := inv_pos.2 hβ
  have := mul_lt_mul_of_pos_left this hi
  have e2 : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
  linarith

/-- the real set whose sup is the conjugate -/
def cfS (f : E → EReal) (x' : StrongDual ℝ E) : Set ℝ :=
  {t | ∃ y : E, ∃ c : ℝ, f y = c ∧ t = x' y - c - ‖y‖ ^ 2 / 2}

lemma cf_le_norm (x' : StrongDual ℝ E) (y : E) : x' y ≤ ‖x'‖ * ‖y‖ :=
  (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using x'.le_opNorm y)

lemma cfS_bdd {f : E → EReal} (l : StrongDual ℝ E) (b : ℝ) (hl : ∀ y (c : ℝ), f y = c → l y + b ≤ c)
    (x' : StrongDual ℝ E) {t : ℝ} (ht : t ∈ cfS f x') :
    ∃ y : E, t ≤ (‖x'‖ + ‖l‖) * ‖y‖ - b - ‖y‖ ^ 2 / 2 := by
  obtain ⟨y, c, hc, rfl⟩ := ht
  refine ⟨y, ?_⟩
  have h1 := cf_le_norm x' y
  have h2 := cf_le_norm (-l) y
  rw [norm_neg, ContinuousLinearMap.neg_apply] at h2
  have := hl y c hc
  nlinarith

lemma cfS_bddAbove {f : E → EReal} (l : StrongDual ℝ E) (b : ℝ) (hl : ∀ y (c : ℝ), f y = c → l y + b ≤ c)
    (x' : StrongDual ℝ E) : BddAbove (cfS f x') := by
  refine ⟨(‖x'‖ + ‖l‖) ^ 2 / 2 - b, fun t ht => ?_⟩
  obtain ⟨y, hy⟩ := cfS_bdd l b hl x' ht
  nlinarith [sq_nonneg (‖x'‖ + ‖l‖ - ‖y‖)]

theorem conjfin_core {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hlsc : LowerSemicontinuous f) :
    ∃ h : StrongDual ℝ E → ℝ, Continuous h ∧
      ∀ x' : StrongDual ℝ E, Shared.conj (fun y => f y + Shared.halfSqNorm y) x' = ((h x' : ℝ) : EReal) := by
  obtain ⟨l, b, hl⟩ := cf_minorant f hf hlsc
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hne : ∀ x', (cfS f x').Nonempty := fun x' => ⟨_, y0, c0, hc0.symm, rfl⟩
  have hbdd := cfS_bddAbove l b hl
  set H : StrongDual ℝ E → ℝ := fun x' => sSup (cfS f x') with hH
  -- Lipschitz on balls
  have hlip : ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, 0 < M ∧ ∀ x' x'' : StrongDual ℝ E, ‖x'‖ ≤ R → ‖x''‖ ≤ R →
      H x' - H x'' ≤ M * ‖x' - x''‖ := by
    intro R hR
    set N := ‖l‖
    set K := R * ‖y0‖ + |c0| + ‖y0‖ ^ 2 / 2 + 1
    refine ⟨2 * (R + N) + 2 * |K - b| + 1, by positivity, fun x' x'' h1 h2 => ?_⟩
    apply le_of_forall_pos_lt_add
    intro ε hε
    set ε' := min ε 1
    have hε' : 0 < ε' := lt_min hε one_pos
    obtain ⟨t, ht, htlt⟩ := exists_lt_of_lt_csSup (hne x') (show H x' - ε' < H x' by linarith)
    have ht' := ht
    obtain ⟨y, c, hc, rfl⟩ := ht'
    -- lower bound on t
    have ht0 : x' y0 - c0 - ‖y0‖ ^ 2 / 2 ≤ H x' := le_csSup (hbdd x') ⟨y0, c0, hc0.symm, rfl⟩
    have hx'y0 : -(R * ‖y0‖) ≤ x' y0 := by
      have := cf_le_norm (-x') y0
      rw [norm_neg, ContinuousLinearMap.neg_apply] at this
      nlinarith [norm_nonneg y0]
    have hε1 : ε' ≤ 1 := min_le_right _ _
    have hlow : -K < x' y - c - ‖y‖ ^ 2 / 2 := by
      have := le_abs_self c0
      simp only [K]; linarith
    have hup : x' y - c - ‖y‖ ^ 2 / 2 ≤ (R + N) * ‖y‖ - b - ‖y‖ ^ 2 / 2 := by
      have a1 := cf_le_norm x' y
      have a2 := cf_le_norm (-l) y
      rw [norm_neg, ContinuousLinearMap.neg_apply] at a2
      have := hl y c hc
      have : ‖x'‖ * ‖y‖ ≤ R * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg y)
      linarith
    have hn : ‖y‖ ≤ 2 * (R + N) + 2 * |K - b| + 1 := by
      by_contra hcon
      push_neg at hcon
      have hN : 0 ≤ N := norm_nonneg _
      have habs := le_abs_self (K - b)
      have habs0 := abs_nonneg (K - b)
      have hy1 : 1 ≤ ‖y‖ := by linarith
      nlinarith
    have hH2 : x'' y - c - ‖y‖ ^ 2 / 2 ≤ H x'' := le_csSup (hbdd x'') ⟨y, c, hc, rfl⟩
    have hd : x' y - x'' y ≤ ‖x' - x''‖ * ‖y‖ := by
      have := cf_le_norm (x' - x'') y
      simpa using this
    have : ‖x' - x''‖ * ‖y‖ ≤ ‖x' - x''‖ * (2 * (R + N) + 2 * |K - b| + 1) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    have hεε : ε' ≤ ε := min_le_left _ _
    linarith
  refine ⟨H, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x'
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨M, hM, hMl⟩ := hlip (‖x'‖ + 1) (by positivity)
    refine ⟨min 1 (ε / (2 * M)), lt_min one_pos (by positivity), fun x'' hd => ?_⟩
    rw [dist_eq_norm] at hd
    have hd1 : ‖x'' - x'‖ < 1 := lt_of_lt_of_le hd (min_le_left _ _)
    have hd2 : ‖x'' - x'‖ < ε / (2 * M) := lt_of_lt_of_le hd (min_le_right _ _)
    have hn1 : ‖x''‖ ≤ ‖x'‖ + 1 := by
      have := norm_le_insert' x'' x'
      linarith [norm_sub_rev x'' x']
    have a1 := hMl x' x'' (by linarith) hn1
    have a2 := hMl x'' x' hn1 (by linarith)
    rw [norm_sub_rev] at a1
    have : M * ‖x'' - x'‖ < ε / 2 := by
      calc M * ‖x'' - x'‖ < M * (ε / (2 * M)) := mul_lt_mul_of_pos_left hd2 hM
        _ = ε / 2 := by field_simp
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  · intro x'
    unfold Shared.conj Shared.halfSqNorm
    apply le_antisymm
    · apply iSup_le
      intro y
      beta_reduce
      rcases eq_or_ne (f y) ⊤ with hy | hy
      · rw [hy, EReal.top_add_coe, EReal.sub_top]; exact bot_le
      lift f y to ℝ using ⟨hy, hf.1 y⟩ with c hc
      rw [← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      apply le_csSup (hbdd x')
      exact ⟨y, c, hc.symm, by ring⟩
    · by_contra hlt
      push_neg at hlt
      obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
      rw [EReal.coe_lt_coe_iff] at hz2
      obtain ⟨t, ⟨y, c, hc, rfl⟩, htz⟩ := exists_lt_of_lt_csSup (hne x') hz2
      have : ((x' y : ℝ) : EReal) - (f y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) ≤
          ⨆ y, ((x' y : ℝ) : EReal) - (f y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal)) :=
        le_iSup (fun y => ((x' y : ℝ) : EReal) - (f y + ((‖y‖ ^ 2 / 2 : ℝ) : EReal))) y
      rw [hc, ← EReal.coe_add, ← EReal.coe_sub] at this
      have h3 := lt_of_le_of_lt this hz1
      rw [EReal.coe_lt_coe_iff] at h3
      linarith

end ConjFin
end RockafellarMaxMono.Cyclic.AcceptedConjFin

open RockafellarMaxMono.Cyclic.AcceptedConjFin
open RockafellarMaxMono

theorem uniqueness_accepted_conjfin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hlsc : LowerSemicontinuous f) :
    ∃ h : StrongDual ℝ E → ℝ, Continuous h ∧
      ∀ x' : StrongDual ℝ E, Shared.conj (fun y => f y + Shared.halfSqNorm y) x' = ((h x' : ℝ) : EReal) := by
  exact conjfin_core f hf hlsc
end

section



namespace RockafellarMaxMono.Cyclic.AcceptedBiconj

section Biconj
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma cf_minorant (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∃ (l : StrongDual ℝ E) (b : ℝ), ∀ y (c : ℝ), f y = c → l y + b ≤ c := by
  set C : Set (E × ℝ) := {p | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hC
  have hCc : IsClosed C := by
    have : C = (Prod.map id (fun r : ℝ => (r : EReal))) ⁻¹' {p : E × EReal | f p.1 ≤ p.2} := by
      ext p; simp [hC]
    rw [this]
    exact hlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  have hCv : Convex ℝ C := by
    rintro ⟨y1, r1⟩ h1 ⟨y2, r2⟩ h2 s t hs ht hst
    simp only [hC, Set.mem_setOf_eq] at h1 h2 ⊢
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      simpa using h1
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · subst hs0
      have : t = 1 := by linarith
      subst this
      simpa using h2
    have hts : s = 1 - t := by linarith
    subst hts
    have hne1 : f y1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hne2 : f y2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hcv := hf.2.2 y1 y2 t ht0 (by linarith)
    lift f y1 to ℝ using ⟨hne1, hf.1 y1⟩ with c1
    lift f y2 to ℝ using ⟨hne2, hf.1 y2⟩ with c2
    rw [EReal.coe_le_coe_iff] at h1 h2
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hcv
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine hcv.trans ?_
    rw [EReal.coe_le_coe_iff]
    nlinarith
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hnot : (y0, c0 - 1) ∉ C := by
    simp only [hC, Set.mem_setOf_eq, ← hc0, EReal.coe_le_coe_iff, not_le]; linarith
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hCv hCc hnot
  set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set β : ℝ := ℓ (0, 1) with hβ
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have h0 := hl2 (y0, c0) (by simp [hC, ← hc0])
  rw [hℓ] at hl1 h0
  have hβ : 0 < β := by nlinarith
  refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_⟩
  have := hl2 (y, c) (by simp [hC, hc])
  rw [hℓ] at this
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
  have e : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  have hi : 0 < β⁻¹ := inv_pos.2 hβ
  have := mul_lt_mul_of_pos_left this hi
  have e2 : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
  linarith


lemma bc_sep (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x : E) (z : ℝ) (hz : (z : EReal) < f x) :
    ∃ (l : StrongDual ℝ E) (b : ℝ), (∀ y (c : ℝ), f y = c → l y + b ≤ c) ∧ z < l x + b := by
  obtain ⟨l0, b0, hl0⟩ := cf_minorant f hf hlsc
  set C : Set (E × ℝ) := {p | f p.1 ≤ ((p.2 : ℝ) : EReal)} with hC
  have hCc : IsClosed C := by
    have : C = (Prod.map id (fun r : ℝ => (r : EReal))) ⁻¹' {p : E × EReal | f p.1 ≤ p.2} := by
      ext p; simp [hC]
    rw [this]
    exact hlsc.isClosed_epigraph.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  have hCv : Convex ℝ C := by
    rintro ⟨y1, r1⟩ h1 ⟨y2, r2⟩ h2 s t hs ht hst
    simp only [hC, Set.mem_setOf_eq] at h1 h2 ⊢
    rcases eq_or_lt_of_le ht with ht0 | ht0
    · subst ht0
      have : s = 1 := by linarith
      subst this
      simpa using h1
    rcases eq_or_lt_of_le hs with hs0 | hs0
    · subst hs0
      have : t = 1 := by linarith
      subst this
      simpa using h2
    have hts : s = 1 - t := by linarith
    subst hts
    have hne1 : f y1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hne2 : f y2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h2
    have hcv := hf.2.2 y1 y2 t ht0 (by linarith)
    lift f y1 to ℝ using ⟨hne1, hf.1 y1⟩ with c1
    lift f y2 to ℝ using ⟨hne2, hf.1 y2⟩ with c2
    rw [EReal.coe_le_coe_iff] at h1 h2
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at hcv
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine hcv.trans ?_
    rw [EReal.coe_le_coe_iff]
    nlinarith
  have hnot : (x, z) ∉ C := by
    simp only [hC, Set.mem_setOf_eq, not_le]; exact hz
  obtain ⟨ℓ, u, hl1, hl2⟩ := geometric_hahn_banach_point_closed hCv hCc hnot
  set φ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hφ
  set β : ℝ := ℓ (0, 1) with hβ
  have hℓ : ∀ y r, ℓ (y, r) = φ y + r * β := by
    intro y r
    have : (y, r) = ((y, 0) : E × ℝ) + r • ((0, 1) : E × ℝ) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  rw [hℓ] at hl1
  have hC' : ∀ y (c : ℝ), f y = c → ∀ r, c ≤ r → u < φ y + r * β := by
    intro y c hc r hr
    have := hl2 (y, r) (by simp [hC, hc, hr])
    rwa [hℓ] at this
  obtain ⟨y0, hy0⟩ := hf.2.1
  lift f y0 to ℝ using ⟨hy0, hf.1 y0⟩ with c0 hc0
  have hβ0 : 0 ≤ β := by
    by_contra hneg
    push_neg at hneg
    set r := max c0 ((u - φ y0) / β)
    have h1 := hC' y0 c0 hc0.symm r (le_max_left _ _)
    have h2 : (u - φ y0) / β ≤ r := le_max_right _ _
    rw [div_le_iff_of_neg hneg] at h2
    linarith
  rcases eq_or_lt_of_le hβ0 with hβ0 | hβpos
  · -- vertical hyperplane
    have hβ' : β = 0 := hβ0.symm
    rw [hβ', mul_zero, add_zero] at hl1
    have hdom : ∀ y (c : ℝ), f y = c → u < φ y := by
      intro y c hc
      have := hC' y c hc c le_rfl
      rwa [hβ', mul_zero, add_zero] at this
    have hpos : 0 < u - φ x := by linarith
    set lam := max 0 ((z - l0 x - b0) / (u - φ x)) + 1 with hlam
    have hlam0 : 0 < lam := by positivity
    refine ⟨l0 - lam • φ, b0 + lam * u, fun y c hc => ?_, ?_⟩
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have := hl0 y c hc
      have := hdom y c hc
      nlinarith
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h1 : (z - l0 x - b0) / (u - φ x) ≤ max 0 ((z - l0 x - b0) / (u - φ x)) := le_max_right _ _
      rw [div_le_iff₀ hpos] at h1
      have h2 : lam * (u - φ x) = max 0 ((z - l0 x - b0) / (u - φ x)) * (u - φ x) + (u - φ x) := by
        rw [hlam]; ring
      nlinarith
  · refine ⟨-(β⁻¹ • φ), u / β, fun y c hc => ?_, ?_⟩
    · have := hC' y c hc c le_rfl
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have := mul_lt_mul_of_pos_left this hi
      have e2 : β⁻¹ * (φ y + c * β) = β⁻¹ * φ y + c := by field_simp
      linarith
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]
      have hi : 0 < β⁻¹ := inv_pos.2 hβpos
      have := mul_lt_mul_of_pos_left hl1 hi
      have e2 : β⁻¹ * (φ x + z * β) = β⁻¹ * φ x + z := by field_simp
      linarith

theorem biconj_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.conj (Shared.conj f) (NormedSpace.inclusionInDoubleDual ℝ E x) = f x := by
  intro x
  unfold Shared.conj
  simp only [NormedSpace.dual_def]
  apply le_antisymm
  · apply iSup_le
    intro x'
    rcases eq_or_ne (f x) ⊤ with hx | hx
    · rw [hx]; exact le_top
    lift f x to ℝ using ⟨hx, hf.1 x⟩ with a ha
    have h1 : ((x' x - a : ℝ) : EReal) ≤ ⨆ y, ((x' y : ℝ) : EReal) - f y := by
      have := le_iSup (fun y => ((x' y : ℝ) : EReal) - f y) x
      rwa [← ha, ← EReal.coe_sub] at this
    calc ((x' x : ℝ) : EReal) - ⨆ y, ((x' y : ℝ) : EReal) - f y
        ≤ ((x' x : ℝ) : EReal) - ((x' x - a : ℝ) : EReal) := EReal.sub_le_sub le_rfl h1
      _ = (a : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
  · by_contra hlt
    push_neg at hlt
    obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
    obtain ⟨l, b, hl, hlz⟩ := bc_sep f hf hlsc x z hz2
    have hconj : (⨆ y, ((l y : ℝ) : EReal) - f y) ≤ ((-b : ℝ) : EReal) := by
      apply iSup_le
      intro y
      rcases eq_or_ne (f y) ⊤ with hy | hy
      · rw [hy, EReal.sub_top]; exact bot_le
      lift f y to ℝ using ⟨hy, hf.1 y⟩ with c hc
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      have := hl y c hc.symm
      linarith
    have h2 : ((l x + b : ℝ) : EReal) ≤ ((l x : ℝ) : EReal) - ⨆ y, ((l y : ℝ) : EReal) - f y := by
      calc ((l x + b : ℝ) : EReal) = ((l x : ℝ) : EReal) - ((-b : ℝ) : EReal) := by
            rw [← EReal.coe_sub]; congr 1; ring
        _ ≤ _ := EReal.sub_le_sub le_rfl hconj
    have h3 := le_iSup (fun x' : StrongDual ℝ E =>
      ((x' x : ℝ) : EReal) - ⨆ y, ((x' y : ℝ) : EReal) - f y) l
    have h4 := lt_of_le_of_lt (h2.trans h3) hz1
    rw [EReal.coe_lt_coe_iff] at h4
    linarith

end Biconj
end RockafellarMaxMono.Cyclic.AcceptedBiconj

open RockafellarMaxMono.Cyclic.AcceptedBiconj
open RockafellarMaxMono

theorem uniqueness_accepted_biconj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ x : E, Shared.conj (Shared.conj f) (NormedSpace.inclusionInDoubleDual ℝ E x) = f x := by
  exact biconj_core f hf hlsc
end
end

section

section
set_option autoImplicit false
open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conj_term_finite (f : E → EReal) (hf : Shared.ProperConvex f)
    (x : E) (hx : f x ≠ ⊤) (v : StrongDual ℝ E) :
    ((v x:ℝ):EReal)-f x = ((v x-(f x).toReal:ℝ):EReal) := by
  rw [← EReal.coe_toReal hx (hf.1 x),← EReal.coe_sub]
  simp only [EReal.toReal_coe]

theorem conj_ne_bot (f : E → EReal) (hf : Shared.ProperConvex f)
    (v : StrongDual ℝ E) : Shared.conj f v ≠ ⊥ := by
  obtain ⟨x,hx⟩ := hf.2.1
  have hl := le_iSup (fun y => ((v y:ℝ):EReal)-f y) x
  rw [conj_term_finite f hf x hx v] at hl
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hl)

theorem conj_proper_convex (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) : Shared.ProperConvex (Shared.conj f) := by
  obtain ⟨v,b,hb⟩ := rmm_minorant f hf hl
  refine ⟨conj_ne_bot f hf,⟨v,?_⟩,?_⟩
  · have hu : Shared.conj f v ≤ ((-b:ℝ):EReal) := by
      apply iSup_le
      intro x
      by_cases hx : f x=⊤
      · simp only [hx,EReal.sub_top]; exact bot_le
      · rw [conj_term_finite f hf x hx v]
        apply EReal.coe_le_coe_iff.mpr
        linarith [hb x hx]
    exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hu
  · intro v w t ht ht1
    apply iSup_le
    intro x
    by_cases hx : f x=⊤
    · simp only [hx,EReal.sub_top]; exact bot_le
    · rw [conj_term_finite f hf x hx _]
      have he : (((((1-t) • v+t • w) x)-(f x).toReal:ℝ):EReal) =
          ((1-t:ℝ):EReal)*((v x-(f x).toReal:ℝ):EReal)+
            (t:EReal)*((w x-(f x).toReal:ℝ):EReal) := by
        simp only [add_apply,smul_apply,smul_eq_mul,← EReal.coe_mul,← EReal.coe_add]
        congr 1
        ring
      rw [he]
      have hv : ((v x-(f x).toReal:ℝ):EReal) ≤ Shared.conj f v := by
        rw [← conj_term_finite f hf x hx v]
        exact le_iSup (fun y => ((v y:ℝ):EReal)-f y) x
      have hw : ((w x-(f x).toReal:ℝ):EReal) ≤ Shared.conj f w := by
        rw [← conj_term_finite f hf x hx w]
        exact le_iSup (fun y => ((w y:ℝ):EReal)-f y) x
      exact add_le_add
        (mul_le_mul_of_nonneg_left hv (EReal.coe_nonneg.mpr (by linarith)))
        (mul_le_mul_of_nonneg_left hw (EReal.coe_nonneg.mpr ht.le))

theorem conj_lsc (f : E → EReal) (hf : Shared.ProperConvex f) :
    LowerSemicontinuous (Shared.conj f) := by
  apply lowerSemicontinuous_iSup
  intro x
  by_cases hx : f x=⊤
  · simp only [hx,EReal.sub_top]
    exact lowerSemicontinuous_const
  · have he : (fun v : StrongDual ℝ E => ((v x:ℝ):EReal)-f x) =
        (fun v : StrongDual ℝ E => ((v x-(f x).toReal:ℝ):EReal)) := by
      funext v
      exact conj_term_finite f hf x hx v
    rw [he]
    have hc : Continuous (fun v : StrongDual ℝ E => v x-(f x).toReal) := by fun_prop
    exact (continuous_coe_real_ereal.comp hc).lowerSemicontinuous

theorem conj_value_of_subdiff (f : E → EReal) (hf : Shared.ProperConvex f)
    (x : E) (v : StrongDual ℝ E) (hv : v ∈ Shared.subdiff f x) :
    Shared.conj f v=((v x-(f x).toReal:ℝ):EReal) := by
  have hx := rmm_subdiff_fin f hf x v hv
  apply le_antisymm
  · apply iSup_le
    intro y
    by_cases hy : f y=⊤
    · simp only [hy,EReal.sub_top]; exact bot_le
    · rw [conj_term_finite f hf y hy v]
      apply EReal.coe_le_coe_iff.mpr
      have hs := hv y
      rw [← EReal.coe_toReal hx (hf.1 x),← EReal.coe_toReal hy (hf.1 y),← EReal.coe_add] at hs
      have hr := EReal.coe_le_coe_iff.mp hs
      simp only [map_sub] at hr
      linarith
  · rw [← conj_term_finite f hf x hx v]
    exact le_iSup (fun y => ((v y:ℝ):EReal)-f y) x

theorem subdiff_to_conj_subdiff (f : E → EReal) (hf : Shared.ProperConvex f)
    (x : E) (v : StrongDual ℝ E) (hv : v ∈ Shared.subdiff f x) :
    NormedSpace.inclusionInDoubleDual ℝ E x ∈ Shared.subdiff (Shared.conj f) v := by
  intro w
  rw [conj_value_of_subdiff f hf x v hv,← EReal.coe_add]
  have he : (v x-(f x).toReal)+NormedSpace.inclusionInDoubleDual ℝ E x (w-v)=
      w x-(f x).toReal := by simp [map_sub]
  rw [he]
  rw [← conj_term_finite f hf x (rmm_subdiff_fin f hf x v hv) w]
  exact le_iSup (fun y => ((w y:ℝ):EReal)-f y) x

/-- Bounded primal points permit a moving dual covector in the pairing limit. -/
theorem bounded_pairing_tendsto {I : Type*} (l : Filter I)
    (xs : I → E) (vs : I → StrongDual ℝ E) (v : StrongDual ℝ E)
    (z : StrongDual ℝ (StrongDual ℝ E))
    (hv : Tendsto vs l (nhds v)) (C : ℝ) (hb : ∀ i, ‖xs i‖ ≤ C)
    (hz : ∀ w : StrongDual ℝ E, Tendsto (fun i => w (xs i)) l (nhds (z w))) :
    Tendsto (fun i => vs i (xs i)) l (nhds (z v)) := by
  have hn : Tendsto (fun i => ‖vs i-v‖ * C) l (nhds 0) := by
    simpa using (hv.sub (tendsto_const_nhds : Tendsto (fun _ : I => v) l (nhds v))).norm.mul_const C
  have hd : Tendsto (fun i => (vs i-v) (xs i)) l (nhds 0) := by
    apply squeeze_zero_norm _ hn
    intro i
    exact ((vs i-v).le_opNorm (xs i)).trans
      (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
  have ha := hd.add (hz v)
  simpa only [ContinuousLinearMap.sub_apply, sub_add_cancel, zero_add] using ha

/-- The sufficiency direction keeps the original Banach and bounded-net assumptions. -/
theorem bounded_net_conj_subdiff [CompleteSpace E] {I : Type*}
    (l : Filter I) [NeBot l] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) (xs : I → E) (vs : I → StrongDual ℝ E)
    (v : StrongDual ℝ E) (z : StrongDual ℝ (StrongDual ℝ E))
    (hv : Tendsto vs l (nhds v)) (C : ℝ) (hb : ∀ i, ‖xs i‖ ≤ C)
    (hz : ∀ w : StrongDual ℝ E, Tendsto (fun i => w (xs i)) l (nhds (z w)))
    (hs : ∀ i, vs i ∈ Shared.subdiff f (xs i)) :
    z ∈ Shared.subdiff (Shared.conj f) v := by
  have hcf := conj_proper_convex f hf hl
  have hcl := conj_lsc f hf
  apply rmm_key (Shared.conj f) hcf hcl v z
  intro w y hy
  have hm := (bregman_existence_accepted_subdiff_maximal (Shared.conj f) hcf hcl).1
  have hp := bounded_pairing_tendsto l xs vs v z hv C hb hz
  have hyvs : Tendsto (fun i => y (vs i)) l (nhds (y v)) :=
    y.continuous.tendsto v |>.comp hv
  have ht : Tendsto (fun i => y w-y (vs i)-(w (xs i)-vs i (xs i))) l
      (nhds (y w-y v-(z w-z v))) :=
    (tendsto_const_nhds.sub hyvs).sub ((hz w).sub hp)
  have hnon : ∀ i, 0 ≤ y w-y (vs i)-(w (xs i)-vs i (xs i)) := by
    intro i
    have hh := hm w (vs i) y (NormedSpace.inclusionInDoubleDual ℝ E (xs i)) hy
      (subdiff_to_conj_subdiff f hf (xs i) (vs i) (hs i))
    simp only [ContinuousLinearMap.sub_apply, map_sub, NormedSpace.dual_def] at hh
    linarith
  have hh := ge_of_tendsto' ht hnon
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  linarith

universe u

theorem conj_subdiff_of_original_nets {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x' : StrongDual ℝ E) (x'' : StrongDual ℝ (StrongDual ℝ E))
    (hnet : ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (xs' : I → StrongDual ℝ E) (xs : I → E),
        Tendsto xs' atTop (𝓝 x') ∧
        (∃ C : ℝ, ∀ i, ‖xs i‖ ≤ C) ∧
        (∀ y' : StrongDual ℝ E,
          Tendsto (fun i => NormedSpace.inclusionInDoubleDual ℝ E (xs i) y') atTop (𝓝 (x'' y'))) ∧
        ∀ i, xs' i ∈ Shared.subdiff f (xs i)) :
    x'' ∈ Shared.subdiff (Shared.conj f) x' := by
  obtain ⟨I, horder, hdir, hne, vs, xs, hv, ⟨C,hb⟩, hz, hs⟩ := hnet
  letI : PartialOrder I := horder
  letI : IsDirected I (· ≤ ·) := hdir
  letI : Nonempty I := hne
  exact bounded_net_conj_subdiff atTop f hf hlsc xs vs x' x'' hv C hb hz hs

/-- A finite Fenchel-gap bound is exactly the global approximate support inequality. -/
theorem conj_bound_iff_approx_support (f : E → EReal) (hf : Shared.ProperConvex f)
    (x : E) (hx : f x ≠ ⊤) (v : StrongDual ℝ E) (ε : ℝ) :
    Shared.conj f v ≤ ((v x-(f x).toReal+ε : ℝ) : EReal) ↔
    ∀ y, f x+((v (y-x)-ε : ℝ) : EReal) ≤ f y := by
  constructor
  · intro h y
    by_cases hy : f y=⊤
    · rw [hy]; exact le_top
    · have hb := (le_iSup (fun z => ((v z:ℝ):EReal)-f z) y).trans h
      rw [conj_term_finite f hf y hy v,EReal.coe_le_coe_iff] at hb
      rw [← EReal.coe_toReal hx (hf.1 x),← EReal.coe_toReal hy (hf.1 y),
        ← EReal.coe_add,EReal.coe_le_coe_iff]
      simp only [map_sub]
      linarith
  · intro h
    apply iSup_le
    intro y
    by_cases hy : f y=⊤
    · simp only [hy,EReal.sub_top]; exact bot_le
    · have hs := h y
      rw [← EReal.coe_toReal hx (hf.1 x),← EReal.coe_toReal hy (hf.1 y),
        ← EReal.coe_add,EReal.coe_le_coe_iff] at hs
      rw [conj_term_finite f hf y hy v,EReal.coe_le_coe_iff]
      simp only [map_sub] at hs
      linarith
end RockafellarCyclicCodex



end

section

section
section
set_option autoImplicit false
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An open-ball upper bound on a covector also bounds every bidual point inside that ball. -/
theorem bidual_le_of_ball_support (d : StrongDual ℝ E)
    (z : StrongDual ℝ (StrongDual ℝ E)) (R K : ℝ) (hR : ‖z‖ < R)
    (hb : ∀ x : E, ‖x‖ < R → d x ≤ K) : z d ≤ K := by
  have hRpos : 0 < R := lt_of_le_of_lt (norm_nonneg z) hR
  have hK : 0 ≤ K := by simpa using hb 0 (by simpa using hRpos)
  let r : ℝ := (‖z‖+R)/2
  have hrpos : 0 < r := by dsimp [r]; linarith [norm_nonneg z]
  have hrR : r < R := by dsimp [r]; linarith
  have hzr : ‖z‖ ≤ r := by dsimp [r]; linarith
  have hdn : ‖d‖ ≤ K/r := by
    apply d.opNorm_le_bound' (div_nonneg hK hrpos.le)
    intro x hx
    have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    let s : ℝ := r/‖x‖
    have hspos : 0 < s := div_pos hrpos hxpos
    have hscale : ‖s • x‖ = r := by
      rw [norm_smul,Real.norm_of_nonneg hspos.le]
      exact div_mul_cancel₀ r hx
    have hp := hb (s • x) (hscale ▸ hrR)
    have hn := hb (-(s • x)) (by rw [norm_neg,hscale]; exact hrR)
    rw [map_smul,smul_eq_mul] at hp
    rw [map_neg,map_smul,smul_eq_mul] at hn
    have ha : s*|d x| ≤ K := by
      rcases le_total 0 (d x) with h | h
      · rw [abs_of_nonneg h]; exact hp
      · rw [abs_of_nonpos h]; linarith
    rw [Real.norm_eq_abs]
    dsimp [s] at ha
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hrpos).2
    have he : (r/‖x‖)*‖x‖ = r := div_mul_cancel₀ r hx
    have hh := mul_le_mul_of_nonneg_right ha hxpos.le
    have he2 : ((r/‖x‖)*|d x|)*‖x‖ = |d x| * r := by
      rw [mul_right_comm,he]; ring
    rw [he2] at hh
    exact hh
  calc
    z d ≤ ‖z d‖ := le_abs_self _
    _ ≤ ‖z‖*‖d‖ := z.le_opNorm d
    _ ≤ r*‖d‖ := mul_le_mul_of_nonneg_right hzr (norm_nonneg d)
    _ ≤ K := by
      have hh := (le_div_iff₀ hrpos).mp hdn
      nlinarith
end RockafellarCyclicCodex

end
open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A ball-restricted affine lower bound has a global minorant controlling an interior bidual point. -/
theorem affine_minorant_of_ball_minorant (f : E → EReal) (hf : Shared.ProperConvex f)
    (x₀ : E) (hx₀ : f x₀ ≠ ⊤) (R : ℝ) (hxR : ‖x₀‖ < R)
    (z : StrongDual ℝ (StrongDual ℝ E)) (hzR : ‖z‖ < R)
    (w : StrongDual ℝ E) (q : ℝ)
    (hball : ∀ x, ‖x‖ < R → f x ≠ ⊤ → w x-q ≤ (f x).toReal) :
    ∃ (a : StrongDual ℝ E) (b : ℝ),
      (∀ x, f x ≠ ⊤ → a x+b ≤ (f x).toReal) ∧ z w-q ≤ z a+b := by
  classical
  let A : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}
  let B : Set (E × ℝ) := {p | ‖p.1‖ < R ∧ p.2 < w p.1-q}
  have hAconv : Convex ℝ A := by
    simpa [A] using rmm_epi_convex f hf (0 : StrongDual ℝ E) 0
  have hBopen : IsOpen B :=
    (isOpen_lt (continuous_fst.norm) continuous_const).inter
      (isOpen_lt continuous_snd ((w.continuous.comp continuous_fst).sub continuous_const))
  have hBconv : Convex ℝ B := by
    let L : E × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ-
      w.comp (ContinuousLinearMap.fst ℝ E ℝ)
    have hc1 := (convex_ball (0 : E) R).linear_preimage
      (ContinuousLinearMap.fst ℝ E ℝ).toLinearMap
    have hc2 := (convex_Iio (-q)).linear_preimage L.toLinearMap
    have he : B = (ContinuousLinearMap.fst ℝ E ℝ) ⁻¹' Metric.ball 0 R ∩ L ⁻¹' Set.Iio (-q) := by
      ext p
      simp only [B,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,
        Metric.mem_ball,dist_zero_right,Set.mem_Iio]
      change (‖p.1‖ < R ∧ p.2 < w p.1-q) ↔ (‖p.1‖ < R ∧ p.2-w p.1 < -q)
      constructor <;> rintro ⟨hp,hq⟩ <;> exact ⟨hp,by linarith⟩
    rw [he]
    exact hc1.inter hc2
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    intro p hpB hpA
    obtain ⟨hpn,hpr⟩ := hpB
    obtain ⟨hpf,hpv⟩ := (rmm_le_coe f hf p.1 p.2).mp hpA
    have hh := hball p.1 hpn hpf
    linarith
  obtain ⟨ℓ,u,hB,hA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  let β : ℝ := ℓ (0,1)
  have hdec : ∀ y r, ℓ (y,r)=ℓ (y,0)+r*β := by
    intro y r
    have he : ((y,r) : E × ℝ)=(y,0)+r • ((0 : E),(1 : ℝ)) := by ext <;> simp
    rw [he,map_add,map_smul,smul_eq_mul]
  have hxA : (x₀,(f x₀).toReal) ∈ A := by
    change f x₀ ≤ ((f x₀).toReal : EReal)
    rw [EReal.coe_toReal hx₀ (hf.1 x₀)]
  have hxB : (x₀,w x₀-q-1) ∈ B := ⟨hxR,by linarith⟩
  have hβ : 0 < β := by
    have ha := hA _ hxA
    have hb := hB _ hxB
    rw [hdec] at ha hb
    have hg := hball x₀ hxR hx₀
    by_contra h
    have hβn : β ≤ 0 := le_of_not_gt h
    have hh : 0 ≤ ((f x₀).toReal-(w x₀-q-1))*(-β) :=
      mul_nonneg (by linarith) (neg_nonneg.mpr hβn)
    nlinarith
  let a : StrongDual ℝ E := -(β⁻¹) • ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := u/β
  have hab : ∀ y, ℓ (y,0) = -β*a y := by
    intro y
    dsimp [a]
    simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,smul_eq_mul]
    field_simp
  have hb : b*β=u := div_mul_cancel₀ u hβ.ne'
  have hglobal : ∀ x, f x ≠ ⊤ → a x+b ≤ (f x).toReal := by
    intro x hx
    have hp : (x,(f x).toReal) ∈ A := by
      change f x ≤ ((f x).toReal : EReal)
      rw [EReal.coe_toReal hx (hf.1 x)]
    have hh := hA _ hp
    rw [hdec,hab] at hh
    by_contra h
    have hg : 0 < (a x+b-(f x).toReal)*β := mul_pos (by linarith) hβ
    nlinarith
  have hbound : ∀ y, ‖y‖ < R → (w-a) y ≤ q+b := by
    intro y hy
    apply le_of_forall_pos_le_add
    intro ε hε
    have hp : (y,w y-q-ε) ∈ B := ⟨hy,by linarith⟩
    have hh := hB _ hp
    rw [hdec,hab] at hh
    simp only [sub_apply]
    by_contra h
    have hg : 0 < (w y-a y-(q+b+ε))*β := mul_pos (by linarith) hβ
    nlinarith
  have hbid := bidual_le_of_ball_support (w-a) z R (q+b) hzR hbound
  refine ⟨a,b,hglobal,?_⟩
  simp only [map_sub] at hbid
  linarith
end RockafellarCyclicCodex

open RockafellarMaxMono
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def ballRestrict (f : E → EReal) (R : ℝ) : E → EReal := by
  classical
  exact fun x => if ‖x‖ ≤ R then f x else ⊤

theorem conj_antitone (f g : E → EReal) (h : ∀ x, f x ≤ g x) :
    ∀ w, Shared.conj g w ≤ Shared.conj f w := by
  intro w
  apply iSup_mono
  intro x
  exact EReal.sub_le_sub le_rfl (h x)

/-- A ball containing a finite primal point and the bidual point preserves the biconjugate value. -/
theorem biconj_ballRestrict_eq (f : E → EReal) (hf : Shared.ProperConvex f)
    (x₀ : E) (hx₀ : f x₀ ≠ ⊤) (R : ℝ) (hxR : ‖x₀‖ < R)
    (z : StrongDual ℝ (StrongDual ℝ E)) (hzR : ‖z‖ < R) :
    Shared.conj (Shared.conj (ballRestrict f R)) z = Shared.conj (Shared.conj f) z := by
  classical
  have hmajor : ∀ x, f x ≤ ballRestrict f R x := by
    intro x
    dsimp [ballRestrict]
    split_ifs
    · exact le_rfl
    · exact le_top
  have hant := conj_antitone f (ballRestrict f R) hmajor
  apply le_antisymm
  · change (⨆ w, ((z w:ℝ):EReal)-Shared.conj (ballRestrict f R) w) ≤ _
    apply iSup_le
    intro w
    by_cases ht : Shared.conj (ballRestrict f R) w=⊤
    · rw [ht,EReal.sub_top]; exact bot_le
    have hx₀R : ballRestrict f R x₀=f x₀ := by
      dsimp [ballRestrict]; exact if_pos hxR.le
    have hlow := le_iSup (fun x => ((w x:ℝ):EReal)-ballRestrict f R x) x₀
    rw [hx₀R,← EReal.coe_toReal hx₀ (hf.1 x₀),← EReal.coe_sub] at hlow
    have hb : Shared.conj (ballRestrict f R) w ≠ ⊥ :=
      ne_of_gt ((EReal.bot_lt_coe _).trans_le hlow)
    let cw : ℝ := (Shared.conj (ballRestrict f R) w).toReal
    have hcw : (cw:EReal)=Shared.conj (ballRestrict f R) w := EReal.coe_toReal ht hb
    have hball : ∀ x, ‖x‖ < R → f x ≠ ⊤ → w x-cw ≤ (f x).toReal := by
      intro x hx hy
      have hfx : ballRestrict f R x=f x := by dsimp [ballRestrict]; exact if_pos hx.le
      have hh : ((w x:ℝ):EReal)-ballRestrict f R x ≤ Shared.conj (ballRestrict f R) w :=
        le_iSup (fun y => ((w y:ℝ):EReal)-ballRestrict f R y) x
      rw [hfx,← EReal.coe_toReal hy (hf.1 x),← EReal.coe_sub,← hcw,
        EReal.coe_le_coe_iff] at hh
      linarith
    obtain ⟨a,b,hglobal,hcmp⟩ := affine_minorant_of_ball_minorant f hf x₀ hx₀ R hxR z hzR w cw hball
    have hfa : Shared.conj f a ≤ ((-b:ℝ):EReal) := by
      apply iSup_le
      intro x
      by_cases hx : f x=⊤
      · rw [hx,EReal.sub_top]; exact bot_le
      · rw [← EReal.coe_toReal hx (hf.1 x),← EReal.coe_sub,EReal.coe_le_coe_iff]
        have hh := hglobal x hx
        linarith
    have he : ((z a+b:ℝ):EReal)=((z a:ℝ):EReal)-((-b:ℝ):EReal) := by
      rw [← EReal.coe_sub]
      congr 1
      ring
    have hcand : ((z a+b:ℝ):EReal) ≤ Shared.conj (Shared.conj f) z := by
      rw [he]
      exact (EReal.sub_le_sub le_rfl hfa).trans
        (le_iSup (fun y => ((z y:ℝ):EReal)-Shared.conj f y) a)
    rw [← hcw,← EReal.coe_sub]
    exact (EReal.coe_le_coe_iff.mpr hcmp).trans hcand
  · apply iSup_mono
    intro w
    exact EReal.sub_le_sub le_rfl (hant w)
end RockafellarCyclicCodex
end

section
set_option autoImplicit false
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A functional on finitely many dual evaluations commutes with bidual evaluation. -/
theorem finite_dual_evaluation {ι : Type*} [Fintype ι]
    (w : ι → StrongDual ℝ E) (z : StrongDual ℝ (StrongDual ℝ E))
    (ℓ : StrongDual ℝ ((ι → ℝ) × ℝ)) :
    ∃ a : StrongDual ℝ E,
      (∀ x, ℓ ((fun i => w i x),0)=a x) ∧ ℓ ((fun i => z (w i)),0)=z a := by
  classical
  let q : StrongDual ℝ (ι → ℝ) := ℓ.comp (ContinuousLinearMap.inl ℝ (ι → ℝ) ℝ)
  have hq : ∀ y : ι → ℝ, q y=∑ i, y i*q (Pi.single i (1:ℝ)) := by
    intro y
    have hd : y=∑ i, y i • Pi.single i (1:ℝ) := by
      ext j
      simp [Finset.sum_apply,Pi.single_apply]
    calc
      q y = q (∑ i, y i • Pi.single i (1:ℝ)) := congrArg q hd
      _ = _ := by rw [map_sum]; simp only [map_smul,smul_eq_mul]
  let a : StrongDual ℝ E := ∑ i, q (Pi.single i (1:ℝ)) • w i
  refine ⟨a,?_,?_⟩
  · intro x
    change q (fun i => w i x)=a x
    rw [hq]
    simp [a,sum_apply,smul_apply,smul_eq_mul,mul_comm]
  · change q (fun i => z (w i))=z a
    rw [hq]
    simp [a,map_sum,map_smul,smul_eq_mul,mul_comm]
end RockafellarCyclicCodex
end


open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bounded epigraph realizes all finite dual coordinates of a finite bidual value. -/
theorem bounded_epigraph_finite_coordinates {ι : Type*} [Fintype ι]
    (w : ι → StrongDual ℝ E) (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) (x₀ : E) (hx₀ : f x₀ ≠ ⊤)
    (R : ℝ) (hxR : ‖x₀‖ < R) (z : StrongDual ℝ (StrongDual ℝ E)) (hzR : ‖z‖ < R)
    (r : ℝ) (hr : Shared.conj (Shared.conj f) z=(r:EReal)) :
    ((fun i => z (w i)),r) ∈ closure
      ((fun p : E × ℝ => ((fun i => w i p.1),p.2)) ''
        {p : E × ℝ | ‖p.1‖ ≤ R ∧ f p.1 ≤ (p.2:EReal)}) := by
  classical
  let S : Set (E × ℝ) := {p | ‖p.1‖ ≤ R ∧ f p.1 ≤ (p.2:EReal)}
  let L : E × ℝ →L[ℝ] ((ι → ℝ) × ℝ) :=
    (ContinuousLinearMap.pi w).prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hSconv : Convex ℝ S := by
    have hc1 := (convex_closedBall (0:E) R).linear_preimage
      (ContinuousLinearMap.fst ℝ E ℝ).toLinearMap
    have hc2 := rmm_epi_convex f hf (0:StrongDual ℝ E) 0
    have hc1' : Convex ℝ {p : E × ℝ | ‖p.1‖ ≤ R} := by
      have he : {p : E × ℝ | ‖p.1‖ ≤ R} =
          (ContinuousLinearMap.fst ℝ E ℝ).toLinearMap ⁻¹' Metric.closedBall 0 R := by
        ext p
        change (‖p.1‖ ≤ R) ↔ dist p.1 0 ≤ R
        rw [dist_zero_right]
      rw [he]
      exact hc1
    have hc2' : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2:EReal)} := by simpa using hc2
    exact hc1'.inter hc2' 
  have himg : Convex ℝ (L '' S) := hSconv.linear_image L.toLinearMap
  change ((fun i => z (w i)),r) ∈ closure (L '' S)
  by_contra hnot
  obtain ⟨ℓ,u,hpoint,hsep⟩ := geometric_hahn_banach_point_closed himg.closure isClosed_closure hnot
  obtain ⟨a,ha,haz⟩ := finite_dual_evaluation w z ℓ
  let β : ℝ := ℓ (0,1)
  have hdec : ∀ (y : ι → ℝ) t, ℓ (y,t)=ℓ (y,0)+t*β := by
    intro y t
    have he : ((y,t) : (ι → ℝ) × ℝ)=(y,0)+t • ((0:ι → ℝ),(1:ℝ)) := by ext <;> simp
    rw [he,map_add,map_smul,smul_eq_mul]
  rw [hdec,haz] at hpoint
  have hsrc : ∀ x t, (x,t) ∈ S → u < a x+t*β := by
    intro x t hp
    have hh := hsep (L (x,t)) (subset_closure ⟨(x,t),hp,rfl⟩)
    change u < ℓ ((fun i => w i x),t) at hh
    rw [hdec,ha] at hh
    exact hh
  have hxS : (x₀,(f x₀).toReal) ∈ S := by
    refine ⟨hxR.le,?_⟩
    rw [EReal.coe_toReal hx₀ (hf.1 x₀)]
  have hbase := hsrc x₀ (f x₀).toReal hxS
  have hβ : 0 ≤ β := by
    by_contra h
    have hnβ : β < 0 := lt_of_not_ge h
    let n : ℝ := (a x₀+(f x₀).toReal*β-u+1)/(-β)
    have hn : 0 < n := div_pos (by linarith) (neg_pos.mpr hnβ)
    have hp : (x₀,(f x₀).toReal+n) ∈ S := by
      refine ⟨hxR.le,?_⟩
      exact (rmm_le_coe f hf x₀ ((f x₀).toReal+n)).mpr ⟨hx₀,by linarith⟩
    have hh := hsrc x₀ ((f x₀).toReal+n) hp
    have he : n*β= -(a x₀+(f x₀).toReal*β-u+1) := by
      dsimp [n]
      field_simp [ne_of_lt hnβ]
    nlinarith
  obtain ⟨b₀,c₀,hminor⟩ := rmm_minorant f hf hl
  let m : ℝ := c₀-‖b₀‖*R
  have hheight : ∀ x t, (x,t) ∈ S → m ≤ t := by
    intro x t hp
    obtain ⟨hxn,hfx,hft⟩ : ‖x‖ ≤ R ∧ f x ≠ ⊤ ∧ (f x).toReal ≤ t :=
      ⟨hp.1,(rmm_le_coe f hf x t).mp hp.2⟩
    have hh := hminor x hfx
    have hnorm := b₀.le_opNorm x
    rw [Real.norm_eq_abs] at hnorm
    have hneg := neg_abs_le (b₀ x)
    have hmul := mul_le_mul_of_nonneg_left hxn (norm_nonneg b₀)
    dsimp [m]
    linarith
  let g : ℝ := u-(z a+r*β)
  have hg : 0 < g := by dsimp [g]; linarith
  let δ : ℝ := g/(2*(|r-m|+1))
  have hden : 0 < 2*(|r-m|+1) := by positivity
  have hδ : 0 < δ := div_pos hg hden
  have hδeq : δ*(2*(|r-m|+1))=g := div_mul_cancel₀ g hden.ne'
  have hsmall : δ*(r-m) < g := by
    nlinarith [le_abs_self (r-m),abs_nonneg (r-m)]
  let eta : ℝ := β+δ
  have heta : 0 < eta := by dsimp [eta]; linarith
  have hsupport : ∀ x t, (x,t) ∈ S → u+δ*m ≤ a x+t*eta := by
    intro x t hp
    have hh := hsrc x t hp
    have hm := hheight x t hp
    have hmul := mul_le_mul_of_nonneg_left hm hδ.le
    dsimp [eta]
    nlinarith
  let v : StrongDual ℝ E := -(eta⁻¹) • a
  let b : ℝ := (u+δ*m)/eta
  have hv : ∀ x, eta*v x= -a x := by
    intro x
    dsimp [v]
    simp only [smul_apply,smul_eq_mul]
    field_simp
  have hvz : eta*z v= -z a := by
    dsimp [v]
    rw [map_smul,smul_eq_mul]
    field_simp
  have hb : b*eta=u+δ*m := div_mul_cancel₀ _ heta.ne'
  have hglobal : ∀ x, ‖x‖ ≤ R → f x ≠ ⊤ → v x+b ≤ (f x).toReal := by
    intro x hxn hfx
    have hp : (x,(f x).toReal) ∈ S := by
      refine ⟨hxn,?_⟩
      rw [EReal.coe_toReal hfx (hf.1 x)]
    have hh := hsupport x (f x).toReal hp
    by_contra h
    have hmul : 0 < (v x+b-(f x).toReal)*eta := mul_pos (by linarith) heta
    nlinarith [hv x]
  have hconj : Shared.conj (ballRestrict f R) v ≤ ((-b:ℝ):EReal) := by
    apply iSup_le
    intro x
    by_cases hxn : ‖x‖ ≤ R
    · have he : ballRestrict f R x=f x := by dsimp [ballRestrict]; exact if_pos hxn
      rw [he]
      by_cases hfx : f x=⊤
      · rw [hfx,EReal.sub_top]; exact bot_le
      · rw [← EReal.coe_toReal hfx (hf.1 x),← EReal.coe_sub,EReal.coe_le_coe_iff]
        have hh := hglobal x hxn hfx
        linarith
    · have he : ballRestrict f R x=⊤ := by dsimp [ballRestrict]; exact if_neg hxn
      rw [he,EReal.sub_top]; exact bot_le
  have hstrict : r < z v+b := by
    by_contra h
    have hmul : 0 ≤ (r-(z v+b))*eta := mul_nonneg (by linarith) heta.le
    dsimp [g] at hsmall
    have heq : r*eta=r*β+δ*r := by dsimp [eta]; ring
    nlinarith
  have hval : ((z v+b:ℝ):EReal) ≤ Shared.conj (Shared.conj (ballRestrict f R)) z := by
    have he : ((z v+b:ℝ):EReal)=((z v:ℝ):EReal)-((-b:ℝ):EReal) := by
      rw [← EReal.coe_sub]; congr 1; ring
    rw [he]
    exact (EReal.sub_le_sub le_rfl hconj).trans
      (le_iSup (fun y => ((z y:ℝ):EReal)-Shared.conj (ballRestrict f R) y) v)
  rw [biconj_ballRestrict_eq f hf x₀ hx₀ R hxR z hzR,hr,EReal.coe_le_coe_iff] at hval
  linarith
end RockafellarCyclicCodex


open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bounded_finite_epigraph_approx (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) (x₀ : E) (hx₀ : f x₀ ≠ ⊤)
    (R : ℝ) (hxR : ‖x₀‖ < R) (z : StrongDual ℝ (StrongDual ℝ E)) (hzR : ‖z‖ < R)
    (r : ℝ) (hr : Shared.conj (Shared.conj f) z=(r:EReal))
    (F : Finset (StrongDual ℝ E)) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ R ∧ f x ≠ ⊤ ∧ (f x).toReal < r+ε ∧
      ∀ w ∈ F, |w x-z w| < ε := by
  classical
  have hc := bounded_epigraph_finite_coordinates (fun w : F => w.val)
    f hf hl x₀ hx₀ R hxR z hzR r hr
  obtain ⟨p,⟨⟨x,t⟩,hp,rfl⟩,hd⟩ := (Metric.mem_closure_iff.mp hc) ε hε
  rw [dist_eq_norm] at hd
  have hfirst : ‖(fun w : F => z w.val)-(fun w : F => w.val x)‖ < ε :=
    (norm_fst_le (((fun w : F => z w.val),r)-((fun w : F => w.val x),t))).trans_lt hd
  have hsecond : |r-t| < ε := by
    have hs := (norm_snd_le (((fun w : F => z w.val),r)-((fun w : F => w.val x),t))).trans_lt hd
    simpa only [Prod.snd_sub,Real.norm_eq_abs] using hs
  obtain ⟨hfx,hft⟩ := (rmm_le_coe f hf x t).mp hp.2
  refine ⟨x,hp.1,hfx,?_,?_⟩
  · have hh := (abs_lt.mp hsecond).1
    linarith
  · intro w hw
    have hh := (norm_le_pi_norm
      ((fun w : F => z w.val)-(fun w : F => w.val x)) (⟨w,hw⟩:F)).trans_lt hfirst
    simpa only [Pi.sub_apply,Real.norm_eq_abs,abs_sub_comm] using hh
end RockafellarCyclicCodex
end

section
set_option autoImplicit false

section
set_option autoImplicit false
open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Separation extracts a small exact subgradient correction from norm support. -/
theorem subgradient_of_norm_support (f : E → EReal) (hf : Shared.ProperConvex f)
    (x : E) (hxfin : f x ≠ ⊤) (v : StrongDual ℝ E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hmin : ∀ y, f y ≠ ⊤ → (f x).toReal + v (y-x) ≤ (f y).toReal+δ*‖y-x‖) :
    ∃ ψ : StrongDual ℝ E, ψ+v ∈ Shared.subdiff f x ∧ ‖ψ‖ ≤ δ := by
  classical
  have hfF : ∀ y, f y ≠ ⊤ → f y = (((f y).toReal : ℝ) : EReal) :=
    fun y hy => (EReal.coe_toReal hy (hf.1 y)).symm
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, ∀ y, g y = (f y).toReal-v y := ⟨_,fun _ => rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : E → ℝ, ∀ y, K y = δ*‖y-x‖ := ⟨_,fun _ => rfl⟩
  have hKx : K x = 0 := by rw [hK,sub_self,norm_zero,mul_zero]
  have hKcont : Continuous K := by
    have he : K = fun y => δ*‖y-x‖ := funext hK
    rw [he]; fun_prop
  have hKconv : ∀ (y z : E) (s t : ℝ), 0 ≤ s → 0 ≤ t → s+t=1 →
      K (s • y+t • z) ≤ s*K y+t*K z := by
    intro y z s t hs ht hst
    have he : s • y+t • z-x = s • (y-x)+t • (z-x) := by
      rw [smul_sub,smul_sub,sub_add_sub_comm,← add_smul,hst,one_smul]
    have hn : ‖s • (y-x)+t • (z-x)‖ ≤ s*‖y-x‖+t*‖z-x‖ := by
      calc
        _ ≤ ‖s • (y-x)‖+‖t • (z-x)‖ := norm_add_le _ _
        _ = _ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg hs,Real.norm_of_nonneg ht]
    rw [hK,hK,hK,he]
    nlinarith [mul_le_mul_of_nonneg_left hn hδ]
  have hEk : ∀ y, f y ≠ ⊤ → g x+K x ≤ g y+K y := by
    intro y hy
    have hh := hmin y hy
    rw [hg,hg,hKx,hK y]
    simp only [map_sub] at hh
    linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = g x := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Set (E × ℝ), A = {p : E × ℝ | f p.1 ≤ ((p.2 + v p.1 + κ : ℝ) : EReal)} :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Set (E × ℝ), B = {p : E × ℝ | p.2 < -(K p.1 - K x)} := ⟨_, rfl⟩
  have hAconv : Convex ℝ A := hA ▸ rmm_epi_convex f hf v κ
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
    rw [hg p.1, hg x,hKx,hK p.1] at h1
    rw [hκ, hg x] at hp2
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
    rw [hκ, hg]
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
      rw [hκ, hg y, hg x]
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
  have hsub : ψ + v ∈ Shared.subdiff f x := by
    show ∀ y, f x + (((ψ + v) (y - x) : ℝ) : EReal) ≤ f y
    intro y
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · rw [hfF x hxfin, hfF y hy, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have h1 := hS1 y hy
      rw [hg, hg] at h1
      simp only [ContinuousLinearMap.add_apply, map_sub] at h1 ⊢
      linarith
  refine ⟨ψ,hsub,?_⟩
  apply ψ.opNorm_le_bound hδ
  intro w
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  have hneg := hS2 (x+w)
  have hpos := hS2 (x-w)
  rw [hK,hKx,add_sub_cancel_left] at hneg
  have he : x-w-x = -w := by abel
  rw [hK,hKx,he,map_neg,norm_neg] at hpos
  constructor <;> linarith
end RockafellarCyclicCodex

set_option autoImplicit false
namespace RockafellarCyclicCodex
theorem ekeland_with_distance {X : Type*} [MetricSpace X] [CompleteSpace X] (H : X → ℝ)
    (hH : LowerSemicontinuous H) (m : ℝ) (hm : ∀ x, m ≤ H x) (δ : ℝ) (hδ : 0 < δ) (x₁ : X) :
    ∃ x, H x + δ * dist x x₁ ≤ H x₁ ∧ ∀ y, H x ≤ H y + δ * dist y x := by
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
    exact h1
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


/-- An approximate minimum yields a variational point with a quantitative distance bound. -/
theorem ekeland_near_approx_min {X : Type*} [MetricSpace X] [CompleteSpace X]
    (H : X → ℝ) (hl : LowerSemicontinuous H) (m : ℝ) (hm : ∀ x, m ≤ H x)
    (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (x₀ : X) (hx₀ : H x₀ ≤ m+ε) :
    ∃ x, H x ≤ H x₀ ∧ dist x x₀ ≤ ε/δ ∧
      ∀ y, H x ≤ H y+δ*dist y x := by
  obtain ⟨x,hx,hvar⟩ := ekeland_with_distance H hl m hm δ hδ x₀
  refine ⟨x,?_,?_,hvar⟩
  · have hd := mul_nonneg hδ.le (dist_nonneg (x:=x) (y:=x₀))
    linarith
  · apply (le_div_iff₀ hδ).2
    have hb := hm x
    nlinarith
end RockafellarCyclicCodex



namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Exact subgradients approximate global epsilon support in a general Banach space. -/
theorem exact_subgradient_near_approx_support (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) (x₀ : E) (hx₀ : f x₀ ≠ ⊤) (v : StrongDual ℝ E)
    (ε : ℝ) (hε : 0 ≤ ε) (δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ y, f x₀+((v (y-x₀)-ε : ℝ) : EReal) ≤ f y) :
    ∃ x w, w ∈ Shared.subdiff f x ∧ ‖x-x₀‖ ≤ ε/δ ∧ ‖w-v‖ ≤ δ := by
  classical
  let g : E → ℝ := fun y => (f y).toReal-v (y-x₀)
  let M : ℝ := (f x₀).toReal+1
  let m : ℝ := (f x₀).toReal-ε
  let H : E → ℝ := fun y => if f y=⊤ then M else min (g y) M
  have hgm : ∀ y, f y ≠ ⊤ → m ≤ g y := by
    intro y hy
    have hh := hs y
    rw [← EReal.coe_toReal hx₀ (hf.1 x₀),← EReal.coe_toReal hy (hf.1 y),
      ← EReal.coe_add,EReal.coe_le_coe_iff] at hh
    dsimp [m,g]
    linarith
  have hMl : m ≤ M := by dsimp [m,M]; linarith
  have hHbdd : ∀ y, m ≤ H y := by
    intro y
    dsimp [H]
    split_ifs with hy
    · exact hMl
    · exact le_min (hgm y hy) hMl
  have hHlsc : LowerSemicontinuous H := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : M ≤ c
    · have he : H ⁻¹' Set.Iic c = Set.univ := by
        ext y
        simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_univ,iff_true]
        dsimp [H]
        split_ifs
        · exact hc
        · exact (min_le_right _ _).trans hc
      rw [he]; exact isClosed_univ
    · push Not at hc
      have he : H ⁻¹' Set.Iic c =
          (fun y => ((y,c+v (y-x₀)) : E × ℝ)) ⁻¹'
          {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        ext y
        simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_ofPred_eq]
        rw [rmm_le_coe f hf]
        dsimp [H]
        split_ifs with hy
        · simp only [hy,ne_eq,not_true_eq_false,false_and,iff_false,not_le]
          exact hc
        · rw [min_le_iff]
          dsimp [g]
          constructor
          · rintro (h | h)
            · exact ⟨hy,by linarith⟩
            · linarith
          · rintro ⟨_,h⟩
            left; linarith
      rw [he]
      apply (rmm_epi_closed f hl).preimage
      exact continuous_id.prodMk
        (continuous_const.add (v.continuous.comp (continuous_id.sub continuous_const)))
  have hH₀ : H x₀ = (f x₀).toReal := by
    dsimp [H,g]
    rw [if_neg hx₀,sub_self,map_zero,sub_zero,min_eq_left]
    dsimp [M]; linarith
  have hstart : H x₀ ≤ m+ε := by rw [hH₀]; dsimp [m]; linarith
  obtain ⟨x,hxH,hxd,hvar⟩ := ekeland_near_approx_min H hHlsc m hHbdd δ hδ ε x₀ hstart
  rw [hH₀] at hxH
  have hxfin : f x ≠ ⊤ := by
    intro hx
    have he : H x=M := by dsimp [H]; rw [if_pos hx]
    rw [he] at hxH
    dsimp [M] at hxH
    linarith
  have hHx : H x=g x := by
    have he : H x=min (g x) M := by dsimp [H]; rw [if_neg hxfin]
    rw [he] at hxH ⊢
    rcases min_choice (g x) M with h | h
    · exact h
    · rw [h] at hxH; dsimp [M] at hxH; linarith
  have hsupport : ∀ y, f y ≠ ⊤ →
      (f x).toReal+v (y-x) ≤ (f y).toReal+δ*‖y-x‖ := by
    intro y hy
    have hh := hvar y
    have hHy : H y ≤ g y := by dsimp [H]; rw [if_neg hy]; exact min_le_left _ _
    rw [hHx,dist_eq_norm] at hh
    dsimp [g] at hh hHy
    simp only [map_sub] at hh hHy ⊢
    linarith
  obtain ⟨ψ,hψ,hn⟩ := subgradient_of_norm_support f hf x hxfin v δ hδ.le hsupport
  refine ⟨x,ψ+v,hψ,?_,?_⟩
  · simpa only [dist_eq_norm] using hxd
  · simpa only [add_sub_cancel_right] using hn
end RockafellarCyclicCodex


namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Repair a bounded weak-double-dual net of approximate supports to exact graph points. -/
theorem exact_graph_net_of_approx_support {I : Type*} (l : Filter I)
    (f : E → EReal) (hf : Shared.ProperConvex f) (hl : LowerSemicontinuous f)
    (xs : I → E) (v : StrongDual ℝ E) (z : StrongDual ℝ (StrongDual ℝ E))
    (C : ℝ) (hb : ∀ i, ‖xs i‖ ≤ C)
    (hz : ∀ w : StrongDual ℝ E, Tendsto (fun i => w (xs i)) l (nhds (z w)))
    (eps : I → ℝ) (hepos : ∀ i, 0 < eps i) (heone : ∀ i, eps i ≤ 1)
    (he : Tendsto eps l (nhds 0)) (hfin : ∀ i, f (xs i) ≠ ⊤)
    (hs : ∀ i y, f (xs i)+((v (y-xs i)-(eps i)^2 : ℝ) : EReal) ≤ f y) :
    ∃ (ys : I → E) (vs : I → StrongDual ℝ E),
      Tendsto vs l (nhds v) ∧ (∀ i, ‖ys i‖ ≤ C+1) ∧
      (∀ w : StrongDual ℝ E, Tendsto (fun i => w (ys i)) l (nhds (z w))) ∧
      ∀ i, vs i ∈ Shared.subdiff f (ys i) := by
  classical
  have hrepair : ∀ i, ∃ y w, w ∈ Shared.subdiff f y ∧
      ‖y-xs i‖ ≤ eps i ∧ ‖w-v‖ ≤ eps i := by
    intro i
    have hh := exact_subgradient_near_approx_support f hf hl (xs i) (hfin i) v
      ((eps i)^2) (sq_nonneg _) (eps i) (hepos i) (hs i)
    have heq : (eps i)^2/eps i = eps i := by
      field_simp
    simpa only [heq] using hh
  choose ys vs hgraph hdist hdual using hrepair
  have hd : Tendsto (fun i => vs i-v) l (nhds 0) := squeeze_zero_norm hdual he
  have hv : Tendsto vs l (nhds v) := by
    simpa only [sub_add_cancel,zero_add] using
      hd.add (tendsto_const_nhds : Tendsto (fun _ : I => v) l (nhds v))
  refine ⟨ys,vs,hv,?_,?_,hgraph⟩
  · intro i
    calc
      ‖ys i‖ = ‖(ys i-xs i)+xs i‖ := by rw [sub_add_cancel]
      _ ≤ ‖ys i-xs i‖+‖xs i‖ := norm_add_le _ _
      _ ≤ C+1 := by linarith [hdist i,heone i,hb i]
  · intro w
    have hy : Tendsto (fun i => ys i-xs i) l (nhds 0) := squeeze_zero_norm hdist he
    have hw := (w.continuous.tendsto 0).comp hy
    have ht := hw.add (hz w)
    simpa only [Function.comp_apply,map_sub,map_zero,sub_add_cancel,zero_add] using ht
end RockafellarCyclicCodex


namespace RockafellarCyclicCodex
universe u

theorem original_nets_of_approx_support {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {I : Type u} [PartialOrder I]
    [IsDirected I (· ≤ ·)] [Nonempty I]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hl : LowerSemicontinuous f)
    (xs : I → E) (x' : StrongDual ℝ E) (x'' : StrongDual ℝ (StrongDual ℝ E))
    (C : ℝ) (hb : ∀ i, ‖xs i‖ ≤ C)
    (hz : ∀ w : StrongDual ℝ E, Tendsto (fun i => w (xs i)) atTop (nhds (x'' w)))
    (eps : I → ℝ) (hepos : ∀ i, 0 < eps i) (heone : ∀ i, eps i ≤ 1)
    (he : Tendsto eps atTop (nhds 0)) (hfin : ∀ i, f (xs i) ≠ ⊤)
    (hs : ∀ i y, f (xs i)+((x' (y-xs i)-(eps i)^2 : ℝ) : EReal) ≤ f y) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (xs' : I → StrongDual ℝ E) (xs : I → E),
        Tendsto xs' atTop (𝓝 x') ∧
        (∃ C : ℝ, ∀ i, ‖xs i‖ ≤ C) ∧
        (∀ y' : StrongDual ℝ E,
          Tendsto (fun i => NormedSpace.inclusionInDoubleDual ℝ E (xs i) y') atTop (𝓝 (x'' y'))) ∧
        ∀ i, xs' i ∈ Shared.subdiff f (xs i) := by
  obtain ⟨ys,vs,hv,hbounded,hweak,hgraph⟩ := exact_graph_net_of_approx_support
    atTop f hf hl xs x' x'' C hb hz eps hepos heone he hfin hs
  refine ⟨I,inferInstance,inferInstance,inferInstance,vs,ys,hv,⟨C+1,hbounded⟩,?_,hgraph⟩
  intro w
  simpa only [NormedSpace.dual_def] using hweak w
end RockafellarCyclicCodex
end

section
set_option autoImplicit false
open Filter Topology
namespace RockafellarCyclicCodex
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite evaluation control supplies a bounded directed net in the original universe. -/
theorem bounded_approx_support_net_of_finite_approx (f : E → EReal)
    (v : StrongDual ℝ E) (z : StrongDual ℝ (StrongDual ℝ E)) (C : ℝ)
    (ha : ∀ (F : Finset (StrongDual ℝ E)) (ε : ℝ), 0 < ε →
      ∃ x : E, ‖x‖ ≤ C ∧ f x ≠ ⊤ ∧
        (∀ w ∈ F, |w x-z w| < ε) ∧
        ∀ y, f x+((v (y-x)-ε^2 : ℝ) : EReal) ≤ f y) :
    ∃ (xs : Finset (StrongDual ℝ E) × ℕ → E)
      (eps : Finset (StrongDual ℝ E) × ℕ → ℝ),
      (∀ i, ‖xs i‖ ≤ C) ∧ (∀ i, f (xs i) ≠ ⊤) ∧
      (∀ w : StrongDual ℝ E, Tendsto (fun i => w (xs i)) atTop (nhds (z w))) ∧
      (∀ i, 0 < eps i) ∧ (∀ i, eps i ≤ 1) ∧ Tendsto eps atTop (nhds 0) ∧
      ∀ i y, f (xs i)+((v (y-xs i)-(eps i)^2 : ℝ) : EReal) ≤ f y := by
  classical
  let eps : Finset (StrongDual ℝ E) × ℕ → ℝ := fun i => 1/((i.2 : ℝ)+1)
  have hep : ∀ i, 0 < eps i := by intro i; dsimp [eps]; positivity
  have heone : ∀ i, eps i ≤ 1 := by
    intro i
    dsimp [eps]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (i.2:ℝ)+1)).2
    simp only [one_mul]
    have hn : 0 ≤ (i.2:ℝ) := Nat.cast_nonneg _
    linarith
  have hsnd : Tendsto (Prod.snd : Finset (StrongDual ℝ E) × ℕ → ℕ) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact eventually_atTop.2 ⟨(∅,n),fun i hi => hi.2⟩
  have het : Tendsto eps atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd
  have hchoose : ∀ i : Finset (StrongDual ℝ E) × ℕ, ∃ x : E, ‖x‖ ≤ C ∧
      f x ≠ ⊤ ∧ (∀ w ∈ i.1, |w x-z w| < eps i) ∧
      ∀ y, f x+((v (y-x)-(eps i)^2 : ℝ) : EReal) ≤ f y :=
    fun i => ha i.1 (eps i) (hep i)
  choose xs hbound hfin heval hsupport using hchoose
  refine ⟨xs,eps,hbound,hfin,?_,hep,heone,het,hsupport⟩
  intro w
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hev := het.eventually (gt_mem_nhds hε)
  obtain ⟨i₀,hi₀⟩ := eventually_atTop.1 hev
  refine ⟨(i₀.1 ∪ {w},i₀.2),?_⟩
  intro i hi
  have hsub : i₀.1 ∪ {w} ⊆ i.1 := hi.1
  have hw : w ∈ i.1 := hsub (Finset.mem_union_right _ (Finset.mem_singleton_self w))
  have hlarge : i₀ ≤ i := ⟨Finset.Subset.trans Finset.subset_union_left hsub,hi.2⟩
  have hd : dist (w (xs i)) (z w) < eps i := by
    simpa only [Real.dist_eq] using heval i w hw
  exact hd.trans (hi₀ i hlarge)
end RockafellarCyclicCodex
end

open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
universe u

theorem original_nets_of_finite_approx {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → EReal) (hf : Shared.ProperConvex f) (hl : LowerSemicontinuous f)
    (x' : StrongDual ℝ E) (x'' : StrongDual ℝ (StrongDual ℝ E)) (C : ℝ)
    (ha : ∀ (F : Finset (StrongDual ℝ E)) (ε : ℝ), 0 < ε →
      ∃ x : E, ‖x‖ ≤ C ∧ f x ≠ ⊤ ∧
        (∀ w ∈ F, |w x-x'' w| < ε) ∧
        ∀ y, f x+((x' (y-x)-ε^2 : ℝ) : EReal) ≤ f y) :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (xs' : I → StrongDual ℝ E) (xs : I → E),
        Tendsto xs' atTop (𝓝 x') ∧
        (∃ C : ℝ, ∀ i, ‖xs i‖ ≤ C) ∧
        (∀ y' : StrongDual ℝ E,
          Tendsto (fun i => NormedSpace.inclusionInDoubleDual ℝ E (xs i) y') atTop (𝓝 (x'' y'))) ∧
        ∀ i, xs' i ∈ Shared.subdiff f (xs i) := by
  classical
  obtain ⟨xs,eps,hb,hfin,hz,hepos,heone,he,hs⟩ :=
    bounded_approx_support_net_of_finite_approx f x' x'' C ha
  letI : IsDirected (Finset (StrongDual ℝ E) × ℕ) (· ≤ ·) :=
    ⟨fun i j => ⟨(i.1 ∪ j.1,max i.2 j.2),
      ⟨Finset.subset_union_left,le_max_left _ _⟩,
      ⟨Finset.subset_union_right,le_max_right _ _⟩⟩⟩
  exact original_nets_of_approx_support f hf hl xs x' x'' C hb hz
    eps hepos heone he hfin hs
end RockafellarCyclicCodex
end


open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_approx_of_conj_subdiff (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) (v : StrongDual ℝ E)
    (z : StrongDual ℝ (StrongDual ℝ E)) (hz : z ∈ Shared.subdiff (Shared.conj f) v) :
    ∃ C : ℝ, ∀ (F : Finset (StrongDual ℝ E)) (ε : ℝ), 0 < ε →
      ∃ x : E, ‖x‖ ≤ C ∧ f x ≠ ⊤ ∧ (∀ w ∈ F, |w x-z w| < ε) ∧
        ∀ y, f x+((v (y-x)-ε^2 : ℝ) : EReal) ≤ f y := by
  classical
  have hcf := conj_proper_convex f hf hl
  have hvfin := rmm_subdiff_fin (Shared.conj f) hcf v z hz
  have hvcoe : (((Shared.conj f v).toReal:ℝ):EReal)=Shared.conj f v :=
    EReal.coe_toReal hvfin (hcf.1 v)
  have hr := conj_value_of_subdiff (Shared.conj f) hcf v z hz
  obtain ⟨x₀,hx₀⟩ := hf.2.1
  let R : ℝ := ‖x₀‖+‖z‖+1
  have hxR : ‖x₀‖ < R := by dsimp [R]; linarith [norm_nonneg z]
  have hzR : ‖z‖ < R := by dsimp [R]; linarith [norm_nonneg x₀]
  refine ⟨R,?_⟩
  intro F ε hε
  let τ : ℝ := min ε (ε^2/4)
  have hτ : 0 < τ := lt_min hε (by positivity)
  have hτε : τ ≤ ε := min_le_left _ _
  have hτsq : τ ≤ ε^2/4 := min_le_right _ _
  obtain ⟨x,hxn,hfx,hval,heval⟩ := bounded_finite_epigraph_approx f hf hl x₀ hx₀ R hxR z hzR
    (z v-(Shared.conj f v).toReal) hr (F ∪ {v}) τ hτ
  refine ⟨x,hxn,hfx,?_,?_⟩
  · intro w hw
    exact (heval w (Finset.mem_union_left _ hw)).trans_le hτε
  · apply (conj_bound_iff_approx_support f hf x hfx v (ε^2)).mp
    rw [← hvcoe,EReal.coe_le_coe_iff]
    have he := heval v (Finset.mem_union_right _ (Finset.mem_singleton_self v))
    have hvlow := (abs_lt.mp he).1
    nlinarith
end RockafellarCyclicCodex

open RockafellarMaxMono Filter Topology
universe u
namespace RockafellarMaxMono.Cyclic

theorem conj_subdiff_iff_nets_codex {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x' : StrongDual ℝ E) (x'' : StrongDual ℝ (StrongDual ℝ E)) :
    x'' ∈ Shared.subdiff (Shared.conj f) x' ↔
      ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (xs' : I → StrongDual ℝ E) (xs : I → E),
        Tendsto xs' atTop (𝓝 x') ∧
        (∃ C : ℝ, ∀ i, ‖xs i‖ ≤ C) ∧
        (∀ y' : StrongDual ℝ E,
          Tendsto (fun i => NormedSpace.inclusionInDoubleDual ℝ E (xs i) y') atTop (𝓝 (x'' y'))) ∧
        ∀ i, xs' i ∈ Shared.subdiff f (xs i) := by
  constructor
  · intro hz
    obtain ⟨C,ha⟩ := RockafellarCyclicCodex.finite_approx_of_conj_subdiff f hf hlsc x' x'' hz
    exact RockafellarCyclicCodex.original_nets_of_finite_approx f hf hlsc x' x'' C ha
  · intro hnet
    exact RockafellarCyclicCodex.conj_subdiff_of_original_nets f hf hlsc x' x'' hnet

end RockafellarMaxMono.Cyclic


end


open RockafellarMaxMono Filter Topology Pointwise
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def quadraticRegularize (f : E → EReal) : E → EReal :=
  fun x => f x+Shared.halfSqNorm x

theorem half_sq_norm_real_convex : ConvexOn ℝ Set.univ (fun x : E => ‖x‖^2/2) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy s t hs ht hst
  have hn : ‖s • x+t • y‖ ≤ s*‖x‖+t*‖y‖ := by
    calc
      _ ≤ ‖s • x‖+‖t • y‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg hs,Real.norm_of_nonneg ht]
  have hsq := pow_le_pow_left₀ (norm_nonneg (s • x+t • y)) hn 2
  have hmix : (s*‖x‖+t*‖y‖)^2 ≤ s*‖x‖^2+t*‖y‖^2 := by
    have he : s=1-t := by linarith
    rw [he] at hs ⊢
    nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (‖x‖-‖y‖))]
  simp only [smul_eq_mul]
  nlinarith

theorem quadratic_regularize_proper_convex (f : E → EReal) (hf : Shared.ProperConvex f) :
    Shared.ProperConvex (quadraticRegularize f) := by
  refine ⟨?_,?_,?_⟩
  · intro x
    exact EReal.add_ne_bot_iff.mpr ⟨hf.1 x,EReal.coe_ne_bot _⟩
  · obtain ⟨x,hx⟩ := hf.2.1
    exact ⟨x,EReal.add_ne_top hx (EReal.coe_ne_top _)⟩
  · intro x y t ht ht1
    have hq0 := half_sq_norm_real_convex.2 (Set.mem_univ x) (Set.mem_univ y)
      (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    simp only [smul_eq_mul] at hq0
    have hq : Shared.halfSqNorm ((1-t) • x+t • y) ≤
        ((1-t:ℝ):EReal)*Shared.halfSqNorm x+(t:EReal)*Shared.halfSqNorm y := by
      simpa only [Shared.halfSqNorm,← EReal.coe_mul,← EReal.coe_add] using
        (EReal.coe_le_coe_iff.mpr hq0)
    have hh := add_le_add (hf.2.2 x y t ht ht1) hq
    change f ((1-t) • x+t • y)+Shared.halfSqNorm ((1-t) • x+t • y) ≤
      ((1-t:ℝ):EReal)*(f x+Shared.halfSqNorm x)+(t:EReal)*(f y+Shared.halfSqNorm y)
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (by linarith))
      (EReal.coe_ne_top (1-t)),EReal.left_distrib_of_nonneg_of_ne_top
      (EReal.coe_nonneg.mpr ht.le) (EReal.coe_ne_top t)]
    convert hh using 1 <;> abel

theorem quadratic_regularize_lsc (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) : LowerSemicontinuous (quadraticRegularize f) := by
  have hq : Continuous (fun x : E => Shared.halfSqNorm x) :=
    continuous_coe_real_ereal.comp (by fun_prop)
  apply hl.add' hq.lowerSemicontinuous
  intro x
  by_cases hx : f x=⊤
  · rw [hx]
    exact EReal.continuousAt_add_top_coe _
  · have he : f x=(((f x).toReal:ℝ):EReal) := (EReal.coe_toReal hx (hf.1 x)).symm
    rw [he]
    exact EReal.continuousAt_add_coe_coe _ _
end RockafellarCyclicCodex


open RockafellarMaxMono Filter Topology Pointwise
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem regularized_subdiff_inclusion (f g : E → EReal) (hf : Shared.ProperConvex f)
    (hg : Shared.ProperConvex g) (hsub : ∀ x, Shared.subdiff f x ⊆ Shared.subdiff g x) :
    ∀ x, Shared.subdiff (quadraticRegularize f) x ⊆ Shared.subdiff (quadraticRegularize g) x := by
  intro x
  change Shared.subdiff (fun y => f y+Shared.halfSqNorm y) x ⊆
    Shared.subdiff (fun y => g y+Shared.halfSqNorm y) x
  rw [RockafellarMaxMono.Cyclic.AcceptedSumRule.sumrule_core f hf x,RockafellarMaxMono.Cyclic.AcceptedSumRule.sumrule_core g hg x]
  exact Set.add_subset_add (hsub x) Set.Subset.rfl

theorem regularized_conj_subdiff_inclusion (f g : E → EReal)
    (hf : Shared.ProperConvex f) (hlf : LowerSemicontinuous f)
    (hg : Shared.ProperConvex g) (hlg : LowerSemicontinuous g)
    (hsub : ∀ x, Shared.subdiff f x ⊆ Shared.subdiff g x) :
    ∀ v, Shared.subdiff (Shared.conj (quadraticRegularize f)) v ⊆
      Shared.subdiff (Shared.conj (quadraticRegularize g)) v := by
  intro v z hz
  have hF := quadratic_regularize_proper_convex f hf
  have hlF := quadratic_regularize_lsc f hf hlf
  have hG := quadratic_regularize_proper_convex g hg
  have hlG := quadratic_regularize_lsc g hg hlg
  have hinc := regularized_subdiff_inclusion f g hf hg hsub
  obtain ⟨I,horder,hdir,hne,vs,xs,hv,hb,hweak,hgraph⟩ :=
    (RockafellarMaxMono.Cyclic.conj_subdiff_iff_nets_codex (quadraticRegularize f) hF hlF v z).mp hz
  letI : PartialOrder I := horder
  letI : IsDirected I (· ≤ ·) := hdir
  letI : Nonempty I := hne
  exact (RockafellarMaxMono.Cyclic.conj_subdiff_iff_nets_codex (quadraticRegularize g) hG hlG v z).mpr
    ⟨I,horder,hdir,hne,vs,xs,hv,hb,hweak,fun i => hinc (xs i) (hgraph i)⟩
end RockafellarCyclicCodex


open RockafellarMaxMono Filter Topology
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_convex_of_coe_proper (h : E → ℝ) (hh : Shared.ProperConvex (fun x => (h x:EReal))) :
    ConvexOn ℝ Set.univ h := by
  apply convexOn_iff_forall_pos.mpr
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  have he : a=1-b := by linarith
  have hm := hh.2.2 x y b hb (by linarith)
  rw [← he,← EReal.coe_mul,← EReal.coe_mul,← EReal.coe_add,EReal.coe_le_coe_iff] at hm
  simpa only [smul_eq_mul] using hm

theorem regularized_conj_eq_add_const [CompleteSpace E] (f g : E → EReal)
    (hf : Shared.ProperConvex f) (hlf : LowerSemicontinuous f)
    (hg : Shared.ProperConvex g) (hlg : LowerSemicontinuous g)
    (hsub : ∀ x, Shared.subdiff f x ⊆ Shared.subdiff g x) :
    ∃ c : ℝ, ∀ v, Shared.conj (quadraticRegularize g) v =
      Shared.conj (quadraticRegularize f) v+(c:EReal) := by
  obtain ⟨h,hcont,hh⟩ := uniqueness_accepted_conjfin f hf hlf
  obtain ⟨k,kcont,hk⟩ := uniqueness_accepted_conjfin g hg hlg
  have heh : Shared.conj (quadraticRegularize f)=(fun v => (h v:EReal)) := funext hh
  have hek : Shared.conj (quadraticRegularize g)=(fun v => (k v:EReal)) := funext hk
  have hF := quadratic_regularize_proper_convex f hf
  have hlF := quadratic_regularize_lsc f hf hlf
  have hG := quadratic_regularize_proper_convex g hg
  have hlG := quadratic_regularize_lsc g hg hlg
  have hpc := conj_proper_convex (quadraticRegularize f) hF hlF
  have kpc := conj_proper_convex (quadraticRegularize g) hG hlG
  rw [heh] at hpc
  rw [hek] at kpc
  have hconv := real_convex_of_coe_proper h hpc
  have kconv := real_convex_of_coe_proper k kpc
  have hinc := regularized_conj_subdiff_inclusion f g hf hlf hg hlg hsub
  rw [heh,hek] at hinc
  obtain ⟨c,hc⟩ := uniqueness_accepted_finite h k hconv hcont kconv kcont hinc
  refine ⟨c,?_⟩
  intro v
  rw [heh,hek]
  change (k v:EReal)=(h v:EReal)+(c:EReal)
  rw [hc,← EReal.coe_add]
end RockafellarCyclicCodex

open RockafellarMaxMono
namespace RockafellarCyclicCodex
theorem finite_translation_iSup {ι : Type*} (a : ℝ) (F : ι → EReal) :
    (a:EReal)+(⨆ i, F i) = ⨆ i, (a:EReal)+F i := by
  apply le_antisymm
  · have h : (⨆ i, F i) ≤ (-a:EReal)+(⨆ i, (a:EReal)+F i) := by
      apply iSup_le
      intro i
      have hi := add_le_add (show (-a:EReal) ≤ (-a:EReal) from le_rfl)
        (le_iSup (fun i => (a:EReal)+F i) i)
      simpa only [← add_assoc,← EReal.coe_neg,← EReal.coe_add,neg_add_cancel,EReal.coe_zero,zero_add] using hi
    have hh := add_le_add (show (a:EReal) ≤ (a:EReal) from le_rfl) h
    simpa only [← add_assoc,← EReal.coe_neg,← EReal.coe_add,add_neg_cancel,EReal.coe_zero,zero_add] using hh
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup F i)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem conj_add_real_const (f : E → EReal) (c : ℝ) (v : StrongDual ℝ E) :
    Shared.conj (fun x => f x+(c:EReal)) v=Shared.conj f v+((-c:ℝ):EReal) := by
  have he : ∀ x, ((v x:ℝ):EReal)-(f x+(c:EReal)) =
      ((-c:ℝ):EReal)+(((v x:ℝ):EReal)-f x) := by
    intro x
    simp only [sub_eq_add_neg]
    rw [EReal.neg_add (Or.inr (EReal.coe_ne_top c)) (Or.inr (EReal.coe_ne_bot c))]
    simp only [sub_eq_add_neg,← EReal.coe_neg]
    rw [← add_assoc,add_comm (((v x:ℝ):EReal)+(-f x)) ((-c:ℝ):EReal)]
  change (⨆ x, ((v x:ℝ):EReal)-(f x+(c:EReal))) = _
  simp_rw [he]
  rw [← finite_translation_iSup]
  exact add_comm _ _

theorem general_subdiff_inclusion_unique [CompleteSpace E] (f g : E → EReal)
    (hf : Shared.ProperConvex f) (hlf : LowerSemicontinuous f)
    (hg : Shared.ProperConvex g) (hlg : LowerSemicontinuous g)
    (hsub : ∀ x, Shared.subdiff f x ⊆ Shared.subdiff g x) :
    ∃ c : ℝ, ∀ x, g x=f x+(c:EReal) := by
  obtain ⟨c,hc⟩ := regularized_conj_eq_add_const f g hf hlf hg hlg hsub
  have he : Shared.conj (quadraticRegularize g)=
      (fun v => Shared.conj (quadraticRegularize f) v+(c:EReal)) := funext hc
  have hF := quadratic_regularize_proper_convex f hf
  have hlF := quadratic_regularize_lsc f hf hlf
  have hG := quadratic_regularize_proper_convex g hg
  have hlG := quadratic_regularize_lsc g hg hlg
  have hbF := uniqueness_accepted_biconj (quadraticRegularize f) hF hlF
  have hbG := uniqueness_accepted_biconj (quadraticRegularize g) hG hlG
  refine ⟨-c,?_⟩
  intro x
  have hx : quadraticRegularize g x=quadraticRegularize f x+((-c:ℝ):EReal) := by
    calc
      _ = Shared.conj (Shared.conj (quadraticRegularize g))
          (NormedSpace.inclusionInDoubleDual ℝ E x) := (hbG x).symm
      _ = Shared.conj (Shared.conj (quadraticRegularize f))
          (NormedSpace.inclusionInDoubleDual ℝ E x)+((-c:ℝ):EReal) := by
        rw [he,conj_add_real_const]
      _ = _ := by rw [hbF x]
  let q : ℝ := ‖x‖^2/2
  have ht : g x+(q:EReal)=(f x+((-c:ℝ):EReal))+(q:EReal) := by
    dsimp [quadraticRegularize,Shared.halfSqNorm] at hx
    calc
      _ = (f x+(q:EReal))+((-c:ℝ):EReal) := hx
      _ = _ := by rw [add_assoc,add_comm (q:EReal) ((-c:ℝ):EReal),← add_assoc]
  have hh := congrArg (fun y : EReal => y-(q:EReal)) ht
  simpa only [EReal.add_sub_cancel_right] using hh
end RockafellarCyclicCodex

end

section
set_option autoImplicit false
open RockafellarMaxMono
namespace RockafellarCyclicCodex

theorem subdiff_cyclic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) (hf : Shared.ProperConvex f) :
    Cyclic.IsCyclicallyMonotone (Shared.subdiff f) := by
  classical
  intro n x v hv
  obtain ⟨u,hu⟩ := hf.2.1
  have hfin (i : Fin (n+1)) : f (x i) ≠ ⊤ := by
    intro htop
    have hi := hv i u
    rw [htop,EReal.top_add_coe] at hi
    exact hu (top_le_iff.mp hi)
  have hs (i : Fin (n+1)) : (f (x i)).toReal-(f (x (i+1))).toReal ≤
      v i (x i-x (i+1)) := by
    have hi := hv i (x (i+1))
    rw [← EReal.coe_toReal (hfin i) (hf.1 _),
      ← EReal.coe_toReal (hfin (i+1)) (hf.1 _),← EReal.coe_add] at hi
    have hr := EReal.coe_le_coe_iff.mp hi
    simp only [map_sub] at hr ⊢
    linarith
  have he : ∑ i : Fin (n+1), (f (x (i+1))).toReal = ∑ i : Fin (n+1), (f (x i)).toReal := by
    exact (Equiv.addRight (1 : Fin (n+1))).bijective.sum_comp (fun i => (f (x i)).toReal)
  have ht := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hs i)
  rw [Finset.sum_sub_distrib,he,sub_self] at ht
  exact ht
end RockafellarCyclicCodex

end

section
set_option autoImplicit false
open RockafellarMaxMono
namespace RockafellarCyclicCodex

theorem cyclic_isMonotone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E → Set (StrongDual ℝ E)) (hT : Cyclic.IsCyclicallyMonotone T) :
    Maximality.IsMonotoneOp T := by
  intro x y v w hv hw
  have hh := hT 1 ![x,y] ![v,w] (by intro i; fin_cases i <;> simp [hv,hw])
  simp [Fin.sum_univ_two,map_sub] at hh ⊢
  linarith

theorem subdiff_maximal_cyclic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f)
    (hl : LowerSemicontinuous f) :
    Cyclic.IsMaximalCyclicallyMonotone (Shared.subdiff f) := by
  have hm := bregman_existence_accepted_subdiff_maximal f hf hl
  refine ⟨subdiff_cyclic f hf,?_⟩
  intro T hT hinc x
  exact hm.2 T (cyclic_isMonotone T hT) hinc x

theorem maximal_cyclic_nonempty {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E → Set (StrongDual ℝ E)) (hT : Cyclic.IsMaximalCyclicallyMonotone T) :
    ∃ x v, v ∈ T x := by
  classical
  by_contra hn
  have hempty (x : E) (v : StrongDual ℝ E) : v ∉ T x := fun hv => hn ⟨x,v,hv⟩
  let S : E → Set (StrongDual ℝ E) := fun x => if x=0 then {0} else ∅
  have hS : Cyclic.IsCyclicallyMonotone S := by
    intro n x v hv
    have hz (i : Fin (n+1)) : v i=0 := by
      have hi := hv i
      by_cases hx : x i=0
      · simpa only [S,if_pos hx,Set.mem_singleton_iff] using hi
      · simp only [S,if_neg hx,Set.mem_empty_iff_false] at hi
    simp_rw [hz]
    simp
  have he := hT.2 S hS (fun x v hv => False.elim (hempty x v hv)) 0
  apply hn
  refine ⟨0,0,?_⟩
  rw [← he]
  simp [S]
end RockafellarCyclicCodex

end

section
set_option autoImplicit false
open RockafellarMaxMono
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure GraphPath (T : E → Set (StrongDual ℝ E)) (a : E) where
  n : ℕ
  x : Fin (n+1) → E
  v : Fin (n+1) → StrongDual ℝ E
  root : x 0=a
  mem : ∀ i, v i ∈ T (x i)

noncomputable def GraphPath.cost {T : E → Set (StrongDual ℝ E)} {a : E}
    (p : GraphPath T a) (b : E) : ℝ :=
  (∑ i : Fin p.n, p.v i.castSucc (p.x i.succ-p.x i.castSucc))+
    p.v (Fin.last p.n) (b-p.x (Fin.last p.n))

def GraphPath.single (T : E → Set (StrongDual ℝ E)) (a : E)
    (u : StrongDual ℝ E) (hu : u ∈ T a) : GraphPath T a where
  n := 0
  x := fun _ => a
  v := fun _ => u
  root := rfl
  mem := fun _ => hu

noncomputable def GraphPath.append {T : E → Set (StrongDual ℝ E)} {a : E}
    (p : GraphPath T a) (b : E) (u : StrongDual ℝ E) (hu : u ∈ T b) : GraphPath T a where
  n := p.n+1
  x := Fin.snoc p.x b
  v := Fin.snoc p.v u
  root := by simpa only [Fin.snoc_apply_zero] using p.root
  mem := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hu
    · simpa only [Fin.snoc_castSucc] using p.mem j

theorem GraphPath.single_cost (T : E → Set (StrongDual ℝ E)) (a b : E)
    (u : StrongDual ℝ E) (hu : u ∈ T a) : (GraphPath.single T a u hu).cost b=u (b-a) := by
  simp [GraphPath.cost,GraphPath.single]

theorem GraphPath.append_cost {T : E → Set (StrongDual ℝ E)} {a : E}
    (p : GraphPath T a) (b c : E) (u : StrongDual ℝ E) (hu : u ∈ T b) :
    (p.append b u hu).cost c=p.cost b+u (c-b) := by
  change (∑ i : Fin (p.n+1), (Fin.snoc (α:=fun _ => StrongDual ℝ E) p.v u) i.castSucc
      ((Fin.snoc (α:=fun _ => E) p.x b) i.succ-(Fin.snoc (α:=fun _ => E) p.x b) i.castSucc))+
    (Fin.snoc (α:=fun _ => StrongDual ℝ E) p.v u) (Fin.last (p.n+1)) (c-(Fin.snoc (α:=fun _ => E) p.x b) (Fin.last (p.n+1))) =
    p.cost b+u (c-b)
  rw [Fin.sum_univ_castSucc]
  simp only [← Fin.castSucc_succ,Fin.snoc_castSucc,Fin.succ_last,Fin.snoc_last,GraphPath.cost]

theorem GraphPath.cost_at_root_nonpos {T : E → Set (StrongDual ℝ E)} {a : E}
    (hT : Cyclic.IsCyclicallyMonotone T) (p : GraphPath T a) : p.cost a ≤ 0 := by
  classical
  have h := hT p.n p.x p.v p.mem
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.coeSucc_eq_succ,Fin.last_add_one,p.root] at h
  have he : (∑ i : Fin p.n, p.v i.castSucc (p.x i.castSucc-p.x i.succ)) =
      -(∑ i : Fin p.n, p.v i.castSucc (p.x i.succ-p.x i.castSucc)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_sub]
    ring
  rw [he] at h
  simp only [GraphPath.cost,map_sub] at h ⊢
  linarith

theorem GraphPath.cost_continuous {T : E → Set (StrongDual ℝ E)} {a : E}
    (p : GraphPath T a) : Continuous p.cost := by
  unfold GraphPath.cost
  fun_prop
end RockafellarCyclicCodex

end

section
set_option autoImplicit false
open RockafellarMaxMono
namespace RockafellarCyclicCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def pathPotential (T : E → Set (StrongDual ℝ E)) (a x : E) : EReal :=
  ⨆ p : GraphPath T a, (p.cost x : EReal)

theorem GraphPath.cost_affine {T : E → Set (StrongDual ℝ E)} {a : E}
    (p : GraphPath T a) (x y : E) (t : ℝ) :
    p.cost ((1-t) • x+t • y)=(1-t)*p.cost x+t*p.cost y := by
  simp only [GraphPath.cost,map_sub,map_add,map_smul,smul_eq_mul]
  ring

theorem pathPotential_ne_bot (T : E → Set (StrongDual ℝ E)) (a x : E)
    (u : StrongDual ℝ E) (hu : u ∈ T a) : pathPotential T a x ≠ ⊥ := by
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le
    (le_iSup (fun p : GraphPath T a => (p.cost x:EReal)) (GraphPath.single T a u hu)))

theorem pathPotential_at_root (T : E → Set (StrongDual ℝ E))
    (hT : Cyclic.IsCyclicallyMonotone T) (a : E) (u : StrongDual ℝ E) (hu : u ∈ T a) :
    pathPotential T a a=0 := by
  apply le_antisymm
  · apply iSup_le
    intro p
    exact EReal.coe_le_coe_iff.mpr (p.cost_at_root_nonpos hT)
  · have hh := le_iSup (fun p : GraphPath T a => (p.cost a:EReal)) (GraphPath.single T a u hu)
    simpa only [pathPotential,GraphPath.single_cost,sub_self,map_zero,EReal.coe_zero] using hh

theorem pathPotential_proper_convex (T : E → Set (StrongDual ℝ E))
    (hT : Cyclic.IsCyclicallyMonotone T) (a : E) (u : StrongDual ℝ E) (hu : u ∈ T a) :
    Shared.ProperConvex (pathPotential T a) := by
  refine ⟨fun x => pathPotential_ne_bot T a x u hu,⟨a,?_⟩,?_⟩
  · rw [pathPotential_at_root T hT a u hu]
    exact EReal.zero_ne_top
  · intro x y t ht ht1
    apply iSup_le
    intro p
    rw [p.cost_affine,EReal.coe_add,EReal.coe_mul,EReal.coe_mul]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (le_iSup (fun q : GraphPath T a => (q.cost x:EReal)) p)
        (show (0:EReal) ≤ ((1-t:ℝ):EReal) from EReal.coe_nonneg.mpr (by linarith)))
      (mul_le_mul_of_nonneg_left (le_iSup (fun q : GraphPath T a => (q.cost y:EReal)) p)
        (show (0:EReal) ≤ (t:EReal) from EReal.coe_nonneg.mpr ht.le))

theorem pathPotential_lsc (T : E → Set (StrongDual ℝ E)) (a : E) :
    LowerSemicontinuous (pathPotential T a) := by
  exact lowerSemicontinuous_iSup fun p =>
    (continuous_coe_real_ereal.comp p.cost_continuous).lowerSemicontinuous

/-- Finite real translation commutes with an extended-real supremum, including poles. -/
theorem coe_add_iSup {ι : Type*} (a : ℝ) (F : ι → EReal) :
    (a:EReal)+(⨆ i, F i) = ⨆ i, (a:EReal)+F i := by
  apply le_antisymm
  · have h : (⨆ i, F i) ≤ (-a:EReal)+(⨆ i, (a:EReal)+F i) := by
      apply iSup_le
      intro i
      have hi := add_le_add (show (-a:EReal) ≤ (-a:EReal) from le_rfl)
        (le_iSup (fun i => (a:EReal)+F i) i)
      simpa only [← add_assoc,← EReal.coe_neg,← EReal.coe_add,neg_add_cancel,EReal.coe_zero,zero_add] using hi
    have hh := add_le_add (show (a:EReal) ≤ (a:EReal) from le_rfl) h
    simpa only [← add_assoc,← EReal.coe_neg,← EReal.coe_add,add_neg_cancel,EReal.coe_zero,zero_add] using hh
  · exact iSup_le fun i => add_le_add le_rfl (le_iSup F i)

theorem graph_subset_potential_subdiff (T : E → Set (StrongDual ℝ E)) (a : E) :
    ∀ x, T x ⊆ Shared.subdiff (pathPotential T a) x := by
  intro x u hu y
  rw [add_comm,pathPotential,coe_add_iSup]
  apply iSup_le
  intro p
  have he : ((u (y-x):ℝ):EReal)+(p.cost x:EReal) = ((p.append x u hu).cost y:EReal) := by
    rw [← EReal.coe_add,p.append_cost]
    congr 1
    ring
  rw [he]
  exact le_iSup (fun q : GraphPath T a => (q.cost y:EReal)) (p.append x u hu)

theorem maximal_cyclic_potential (T : E → Set (StrongDual ℝ E))
    (hT : Cyclic.IsMaximalCyclicallyMonotone T) :
    ∃ f : E → EReal, Shared.ProperConvex f ∧ LowerSemicontinuous f ∧
      ∀ x, T x=Shared.subdiff f x := by
  obtain ⟨a,u,hu⟩ := maximal_cyclic_nonempty T hT
  have hp := pathPotential_proper_convex T hT.1 a u hu
  refine ⟨pathPotential T a,hp,pathPotential_lsc T a,?_⟩
  intro x
  exact (hT.2 (Shared.subdiff (pathPotential T a)) (subdiff_cyclic _ hp)
    (graph_subset_potential_subdiff T a) x).symm

theorem maximal_cyclic_iff_subdiff [CompleteSpace E] (T : E → Set (StrongDual ℝ E)) :
    (∃ f : E → EReal, Shared.ProperConvex f ∧ LowerSemicontinuous f ∧
      ∀ x, T x=Shared.subdiff f x) ↔ Cyclic.IsMaximalCyclicallyMonotone T := by
  constructor
  · rintro ⟨f,hf,hl,he⟩
    have hTF : T=Shared.subdiff f := funext he
    rw [hTF]
    exact subdiff_maximal_cyclic f hf hl
  · exact maximal_cyclic_potential T
end RockafellarCyclicCodex

end

section
open RockafellarMaxMono RockafellarMaxMono.Cyclic

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E → Set (StrongDual ℝ E)) :
    ((∃ f : E → EReal, Shared.ProperConvex f ∧ LowerSemicontinuous f ∧ ∀ x, T x = Shared.subdiff f x) ↔
        IsMaximalCyclicallyMonotone T) ∧
      ∀ f g : E → EReal, Shared.ProperConvex f → LowerSemicontinuous f →
        Shared.ProperConvex g → LowerSemicontinuous g →
        (∀ x, T x = Shared.subdiff f x) → (∀ x, T x = Shared.subdiff g x) →
        ∃ c : ℝ, ∀ x, g x = f x + (c : EReal) := by
  refine ⟨RockafellarCyclicCodex.maximal_cyclic_iff_subdiff T,?_⟩
  intro f g hf hflsc hg hglsc hTf hTg
  apply RockafellarCyclicCodex.general_subdiff_inclusion_unique f g hf hflsc hg hglsc
  intro x
  exact ((hTf x).symm.trans (hTg x)).le



end
universe u
open RockafellarMaxMono Filter Topology
namespace RockafellarMaxMono.Cyclic

example {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : E → Set (StrongDual ℝ E)) :
    ((∃ f : E → EReal, Shared.ProperConvex f ∧ LowerSemicontinuous f ∧ ∀ x, T x = Shared.subdiff f x) ↔
        IsMaximalCyclicallyMonotone T) ∧
      ∀ f g : E → EReal, Shared.ProperConvex f → LowerSemicontinuous f →
        Shared.ProperConvex g → LowerSemicontinuous g →
        (∀ x, T x = Shared.subdiff f x) → (∀ x, T x = Shared.subdiff g x) →
        ∃ c : ℝ, ∀ x, g x = f x + (c : EReal) := by
  exact solution T

end RockafellarMaxMono.Cyclic

#print axioms solution
