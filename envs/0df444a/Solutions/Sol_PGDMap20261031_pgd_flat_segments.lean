-- Prove2me | solution 1 for PGDMap20261031.pgd_flat_segments
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-11-01T01:51:55.921136+00:00
-- url     : https://prove2.me/submissions/a0696af0-7e0e-4a03-9746-2fd92405ac19

import Mathlib.Tactic
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_PGDMap20261031_PGD

open PGDMap20261031 Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section

private lemma closed_midpoint_interval (S : Set ℝ) (hc : IsClosed S)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, (a + b) / 2 ∈ S) : Icc (0 : ℝ) 1 ⊆ S := by
  intro t ht
  by_contra hnot
  let A := S ∩ Icc 0 t
  let B := S ∩ Icc t 1
  have hAc : IsCompact A := by simpa [A, inter_comm] using (isCompact_Icc (a := 0) (b := t)).inter_right hc
  have hBc : IsCompact B := by simpa [B, inter_comm] using (isCompact_Icc (a := t) (b := 1)).inter_right hc
  have hAn : A.Nonempty := ⟨0, h0, le_rfl, ht.1⟩
  have hBn : B.Nonempty := ⟨1, h1, ht.2, le_rfl⟩
  obtain ⟨a, ha, ham⟩ := hAc.exists_isMaxOn hAn continuous_id.continuousOn
  obtain ⟨b, hb, hbm⟩ := hBc.exists_isMinOn hBn continuous_id.continuousOn
  have hat : a < t := lt_of_le_of_ne ha.2.2 (by intro h; exact hnot (h ▸ ha.1))
  have htb : t < b := lt_of_le_of_ne hb.2.1 (by intro h; exact hnot (h.symm ▸ hb.1))
  have hmS := hm a ha.1 b hb.1
  by_cases hmt : (a + b) / 2 ≤ t
  · have hmA : (a + b) / 2 ∈ A := ⟨hmS, by linarith [ha.2.1, hb.2.1], hmt⟩
    have : (a + b) / 2 ≤ a := ham hmA
    linarith
  · have hmB : (a + b) / 2 ∈ B :=
      ⟨hmS, (lt_of_not_ge hmt).le, by linarith [ha.2.2, hb.2.2]⟩
    have : b ≤ (a + b) / 2 := hbm hmB
    linarith

private lemma strong_of_midpoint {d : ℕ} (r : Penalty d) (hr : IsPenalty r) (μ : ℝ)
    (hm : ∀ a ∈ r.domain, ∀ b ∈ r.domain,
      r.value ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) ≤
        (r.value a + r.value b) / 2 - μ / 8 * ‖a - b‖ ^ 2) : StrongPenalty r μ := by
  intro x hx y hy t ht
  let w := fun u : ℝ => u • x + (1 - u) • y
  let z := fun u : ℝ => u * r.value x + (1 - u) * r.value y -
    μ / 2 * u * (1 - u) * ‖x - y‖ ^ 2
  let S : Set ℝ := Icc 0 1 ∩ {u | (w u, z u) ∈
    {p : Space d × ℝ | p.1 ∈ r.domain ∧ r.value p.1 ≤ p.2}}
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hS : IsClosed S := isClosed_Icc.inter (hr.2.1.preimage (hw.prodMk hz))
  have h0 : 0 ∈ S := by simp [S, w, z, hy]
  have h1 : 1 ∈ S := by simp [S, w, z, hx]
  have hmid : ∀ a ∈ S, ∀ b ∈ S, (a + b) / 2 ∈ S := by
    intro a ha b hb
    have hc : (a + b) / 2 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [ha.1.1, ha.1.2, hb.1.1, hb.1.2]
    refine ⟨hc, hr.2.2.1 hx hy hc.1 (sub_nonneg.mpr hc.2) (by ring), ?_⟩
    have hmid := hm (w a) ha.2.1 (w b) hb.2.1
    have hwab : (1 / 2 : ℝ) • w a + (1 / 2 : ℝ) • w b = w ((a + b) / 2) := by
      dsimp [w]; module
    have hdif : w a - w b = (a - b) • (x - y) := by dsimp [w]; module
    rw [hwab, hdif, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hmid
    have hza := ha.2.2
    have hzb := hb.2.2
    dsimp [z] at hza hzb ⊢
    nlinarith only [hmid, hza, hzb]
  exact (closed_midpoint_interval S hS h0 h1 hmid ht).2.2

private lemma small_midpoint_gap {d : ℕ} (r : Penalty d) (hr : IsPenalty r)
    (hn : NonSingleton r) (hzero : bestModulus r = 0) (η : ℝ) (hη : 0 < η) :
    ∃ a ∈ r.domain, ∃ b ∈ r.domain, a ≠ b ∧
      (r.value a + r.value b) / 2 -
        r.value ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) < η * ‖a - b‖ ^ 2 := by
  by_contra h
  push_neg at h
  have hstrong : StrongPenalty r (8 * η) := by
    apply strong_of_midpoint r hr
    intro a ha b hb
    by_cases hab : a = b
    · subst b
      simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, sub_zero]
      have heq : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • a = a := by module
      rw [heq]; linarith
    · have := h a ha b hb hab
      linarith
  have hbd : BddAbove {μ : ℝ | 0 ≤ μ ∧ StrongPenalty r μ} := by
    obtain ⟨a, ha, b, hb, hab⟩ := hn
    let D := ‖a - b‖ ^ 2 / 8
    have hD : 0 < D := div_pos (sq_pos_of_pos (norm_sub_pos_iff.mpr hab)) (by norm_num)
    let R := (r.value a + r.value b) / 2 -
      r.value ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b)
    refine ⟨R / D, ?_⟩
    intro μ hμ
    apply (le_div_iff₀ hD).2
    have hm := hμ.2 a ha b hb (1 / 2) ⟨by norm_num, by norm_num⟩
    norm_num at hm
    dsimp [D, R]
    nlinarith only [hm]
  have hle : 8 * η ≤ bestModulus r := le_csSup hbd ⟨by positivity, hstrong⟩
  rw [hzero] at hle
  linarith

private lemma support_interior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (D : Set E) (f : E → ℝ) (hf : ConvexOn ℝ D f)
    (c : E) (hc : c ∈ interior D) :
    ∃ s : E, ∀ y ∈ D, f c + inner ℝ s (y - c) ≤ f y := by
  let C : Set (E × ℝ) := {z | z.1 ∈ interior D ∧ f z.1 < z.2}
  have hCconv : Convex ℝ C := (hf.subset interior_subset hf.1.interior).convex_strict_epigraph
  have hCopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hcont : ContinuousAt (fun z : E × ℝ => f z.1) z :=
      (hf.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hz.1)).comp continuousAt_fst
    have hlt : ∀ᶠ z' in 𝓝 z, f z'.1 < z'.2 := hcont.eventually_lt continuousAt_snd hz.2
    have hD : ∀ᶠ z' in 𝓝 z, z'.1 ∈ interior D :=
      continuousAt_fst.preimage_mem_nhds (isOpen_interior.mem_nhds hz.1)
    exact hD.and hlt
  have hnot : (c, f c) ∉ C := by simp [C]
  obtain ⟨F, hF⟩ := geometric_hahn_banach_point_open hCconv hCopen hnot
  let β : ℝ := F (0, 1)
  have hβ : 0 < β := by
    have h := hF (c, f c + 1) ⟨hc, by linarith⟩
    have heq : (c, f c + 1) = (c, f c) + (0, 1) := by ext <;> simp
    rw [heq, map_add] at h
    dsimp [β]
    linarith
  let G : E →L[ℝ] ℝ := (-β⁻¹) • (F.comp (ContinuousLinearMap.inl ℝ E ℝ))
  refine ⟨(InnerProductSpace.toDual ℝ E).symm G, ?_⟩
  intro y hy
  have hd : F (y - c, 0) + β * (f y - f c) ≥ 0 := by
    have hlim : Tendsto (fun e : ℝ => F (y - c, 0) + β * (f y - f c) + 2 * β * e)
        (𝓝[>] (0 : ℝ)) (𝓝 (F (y - c, 0) + β * (f y - f c))) := by
      have H : Continuous (fun e : ℝ => F (y - c, 0) + β * (f y - f c) + 2 * β * e) := by fun_prop
      simpa using (H.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with e he
    have hm : (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • y ∈ interior D :=
      hf.1.combo_interior_self_mem_interior hc hy (by norm_num) (by norm_num) (by norm_num)
    have hcv := hf.2 (interior_subset hc) hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simp only [smul_eq_mul] at hcv
    have hmem : ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • y,
        (f c + f y) / 2 + e) ∈ C := ⟨hm, by
          change f ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • y) < (f c + f y) / 2 + e
          have he' : 0 < e := he
          linarith⟩
    have h := hF _ hmem
    have hp : ((1 / 2 : ℝ) • c + (1 / 2 : ℝ) • y, (f c + f y) / 2 + e) =
        (c, f c) + (1 / 2 : ℝ) • (y - c, 0) + ((f y - f c) / 2 + e) • (0, 1) := by
      apply Prod.ext
      · change (1 / 2 : ℝ) • c + (1 / 2 : ℝ) • y =
          c + (1 / 2 : ℝ) • (y - c) + ((f y - f c) / 2 + e) • (0 : E)
        module
      · change (f c + f y) / 2 + e = f c + (1 / 2 : ℝ) * 0 + ((f y - f c) / 2 + e) * 1
        ring
    rw [hp, map_add, map_add, map_smul, map_smul] at h
    simp only [smul_eq_mul] at h
    dsimp [β] at hβ ⊢
    linarith
  rw [InnerProductSpace.toDual_symm_apply]
  change f c + (-β⁻¹) * F (y - c, 0) ≤ f y
  have hinv := mul_nonneg hd (inv_nonneg.mpr hβ.le)
  field_simp [ne_of_gt hβ] at hinv ⊢
  nlinarith only [hinv]

private lemma interior_pairs {d : ℕ} (r : Penalty d) (hr : IsPenalty r)
    (a b : Space d) (ha : a ∈ r.domain) (hb : b ∈ r.domain) (hab : a ≠ b)
    (η : ℝ) (hgap : (r.value a + r.value b) / 2 -
      r.value ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) < η * ‖a - b‖ ^ 2) :
    ∃ a' ∈ r.domain, ∃ b' ∈ r.domain, a' ≠ b' ∧
      (r.value a' + r.value b') / 2 -
        r.value ((1 / 2 : ℝ) • a' + (1 / 2 : ℝ) • b') < η * ‖a' - b'‖ ^ 2 ∧
      ∃ s, Supports r ((1 / 2 : ℝ) • a' + (1 / 2 : ℝ) • b') s := by
  let A := affineSpan ℝ r.domain
  let p : A := ⟨a, subset_affineSpan ℝ r.domain ha⟩
  letI : Nonempty A := ⟨p⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ p
  let l : A.direction → Space d := fun z => (e z : Space d)
  have hl (z : A.direction) : l z = (z : Space d) + a := by
    change ((z +ᵥ p : A) : Space d) = _
    exact A.coe_vadd z p
  have hlc : Continuous l := continuous_subtype_val.comp e.continuous
  let D : Set A.direction := l ⁻¹' r.domain
  let f : A.direction → ℝ := r.value ∘ l
  have hf : ConvexOn ℝ D f :=
    hr.2.2.comp_affineMap (A.subtype.comp e.toAffineEquiv.toAffineMap)
  have hDne : (interior D).Nonempty := by
    obtain ⟨q, hq⟩ := hr.1.intrinsicInterior hr.2.2.1
    obtain ⟨q', hq', _⟩ := hq
    refine ⟨e.symm q', ?_⟩
    have hpre := preimage_interior_subset_interior_preimage e.continuous
      (show e (e.symm q') ∈ interior ((↑) ⁻¹' r.domain : Set A) by simpa using hq')
    exact hpre
  obtain ⟨o, ho⟩ := hDne
  let aa : A.direction := ⟨a - a, A.vsub_mem_direction p.property p.property⟩
  let bb : A.direction := ⟨b - a, A.vsub_mem_direction (subset_affineSpan ℝ r.domain hb) p.property⟩
  have hla : l aa = a := by rw [hl]; simp [aa]
  have hlb : l bb = b := by rw [hl]; simp [bb]
  have haa : aa ∈ D := by change l aa ∈ r.domain; rwa [hla]
  have hbb : bb ∈ D := by change l bb ∈ r.domain; rwa [hlb]
  let u := fun t : ℝ => (1 - t) • aa + t • o
  let v := fun t : ℝ => (1 - t) • bb + t • o
  let m := fun t : ℝ => (1 / 2 : ℝ) • u t + (1 / 2 : ℝ) • v t
  let z := fun t : ℝ => ((1 - t) * r.value a + t * f o +
    ((1 - t) * r.value b + t * f o)) / 2 - η * ‖l (u t) - l (v t)‖ ^ 2
  have hluv (t : ℝ) : l (m t) =
      (1 / 2 : ℝ) • l (u t) + (1 / 2 : ℝ) • l (v t) := by
    simp only [hl, m, Submodule.coe_add, Submodule.coe_smul]
    module
  have hmid0 : l (m 0) = (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b := by
    rw [hluv]; simp [u, v, hla, hlb]
  have hz0 : z 0 = (r.value a + r.value b) / 2 - η * ‖a - b‖ ^ 2 := by
    simp [z, u, v, hla, hlb]
  let Epi : Set (Space d × ℝ) := {p | p.1 ∈ r.domain ∧ r.value p.1 ≤ p.2}
  have hnot : (l (m 0), z 0) ∉ Epi := by
    intro h
    have h' := h.2
    rw [hmid0, hz0] at h'
    linarith
  have hmcont : Continuous (fun t => (l (m t), z t)) := by
    dsimp [z, m, u, v]
    exact (hlc.comp (by fun_prop)).prodMk (by fun_prop)
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), (l (m t), z t) ∉ Epi :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), (l (m t), z t) ∉ Epi from
      hmcont.continuousAt.preimage_mem_nhds (hr.2.1.isOpen_compl.mem_nhds hnot)).filter_mono
        nhdsWithin_le_nhds
  have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (show ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 from Iio_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  have htpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht0, ht1, hnt⟩ := (htpos.and (hlt1.and hnear)).exists
  have hui : u t ∈ interior D := by
    have h := hf.1.combo_interior_self_mem_interior ho haa ht0 (by linarith) (by ring : t + (1 - t) = 1)
    change (1 - t) • aa + t • o ∈ interior D
    rw [add_comm]
    exact h
  have hvi : v t ∈ interior D := by
    have h := hf.1.combo_interior_self_mem_interior ho hbb ht0 (by linarith) (by ring : t + (1 - t) = 1)
    change (1 - t) • bb + t • o ∈ interior D
    rw [add_comm]
    exact h
  have hmi : m t ∈ interior D := hf.1.interior hui hvi (by norm_num) (by norm_num) (by norm_num)
  have hua : l (u t) ∈ r.domain := (show u t ∈ D from interior_subset hui)
  have hvb : l (v t) ∈ r.domain := (show v t ∈ D from interior_subset hvi)
  have hmc : l (m t) ∈ r.domain := (show m t ∈ D from interior_subset hmi)
  have hut : r.value (l (u t)) ≤ (1 - t) * r.value a + t * f o := by
    have H := hf.2 haa (interior_subset ho) (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    simpa [u, f, Function.comp_def, hla] using H
  have hvt : r.value (l (v t)) ≤ (1 - t) * r.value b + t * f o := by
    have H := hf.2 hbb (interior_subset ho) (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
    simpa [v, f, Function.comp_def, hlb] using H
  have hdif : l (u t) - l (v t) = (1 - t) • (a - b) := by
    simp only [hl, u, v, Submodule.coe_add, Submodule.coe_smul]
    change ((1 - t) • (a - a) + t • (o : Space d) + a) -
      ((1 - t) • (b - a) + t • (o : Space d) + a) = _
    module
  have hneq : l (u t) ≠ l (v t) := by
    intro h
    have H : (1 - t) • (a - b) = 0 := by rw [← hdif, h, sub_self]
    exact (smul_ne_zero (by linarith) (sub_ne_zero.mpr hab)) H
  refine ⟨l (u t), hua, l (v t), hvb, hneq, ?_, ?_⟩
  · have hzlt : z t < r.value (l (m t)) := lt_of_not_ge (fun h => hnt ⟨hmc, h⟩)
    rw [hluv] at hzlt
    dsimp [z] at hzlt
    linarith
  · obtain ⟨s, hs⟩ := support_interior D f hf (m t) hmi
    refine ⟨(s : Space d), ?_, ?_⟩
    · rwa [← hluv]
    · intro y hy
      let yy : A.direction := ⟨y - a, A.vsub_mem_direction (subset_affineSpan ℝ r.domain hy) p.property⟩
      have hly : l yy = y := by rw [hl]; simp [yy]
      have hyy : yy ∈ D := by change l yy ∈ r.domain; rwa [hly]
      have H := hs yy hyy
      change r.value (l (m t)) + inner ℝ s (yy - m t) ≤ r.value (l yy) at H
      rw [hly, hluv] at H
      have his : inner ℝ (s : Space d) (y - ((1 / 2 : ℝ) • l (u t) + (1 / 2 : ℝ) • l (v t))) =
          inner ℝ s (yy - m t) := by
        rw [← hluv, ← hly, hl, hl]
        simp only [add_sub_add_right_eq_sub, ← Submodule.coe_sub, Submodule.coe_inner]
      rwa [his]

theorem solution : FlatSegmentsClaim := by
  intro d r hr hn hz M hM ε hε
  let η := ε / (8 * M ^ 2)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨a, ha, b, hb, hab, hgap⟩ := small_midpoint_gap r hr hn hz η hη
  obtain ⟨a, ha, b, hb, hab, hgap, s, hs⟩ := interior_pairs r hr a b ha hb hab η hgap
  let c := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b
  let D := ‖b - a‖
  have hD : 0 < D := norm_sub_pos_iff.mpr (Ne.symm hab)
  let v := D⁻¹ • (b - a)
  let δ := D / (2 * M)
  have hδ : 0 < δ := div_pos hD (by positivity)
  have hv : ‖v‖ = 1 := by
    rw [show v = D⁻¹ • (b - a) from rfl, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hD]
    exact inv_mul_cancel₀ (ne_of_gt hD)
  refine ⟨c, s, v, δ, hs, hδ, hv, ?_⟩
  intro t ht
  let α := (M - t) / (2 * M)
  let β := (M + t) / (2 * M)
  have hα : 0 ≤ α := div_nonneg (by linarith [ht.2]) (by positivity)
  have hβ : 0 ≤ β := div_nonneg (by linarith [ht.1]) (by positivity)
  have hsum : α + β = 1 := by dsimp [α, β]; field_simp; ring
  have hα1 : α ≤ 1 := by linarith
  have hβ1 : β ≤ 1 := by linarith
  have heq : c + (δ * t) • v = α • a + β • b := by
    have hsc : δ * t * D⁻¹ = t / (2 * M) := by
      dsimp [δ]
      field_simp [ne_of_gt hD, ne_of_gt hM]
    dsimp [c, v]
    rw [smul_smul, hsc]
    have halpha : α = 1 / 2 - t / (2 * M) := by
      dsimp [α]; field_simp [ne_of_gt hM]
    have hbeta : β = 1 / 2 + t / (2 * M) := by
      dsimp [β]; field_simp [ne_of_gt hM]
    rw [halpha, hbeta]
    module
  have hdom : c + (δ * t) • v ∈ r.domain := by
    rw [heq]; exact hr.2.2.1 ha hb hα hβ hsum
  let A := r.value a - r.value c - inner ℝ s (a - c)
  let B := r.value b - r.value c - inner ℝ s (b - c)
  have hA : 0 ≤ A := by have H := hs.2 a ha; dsimp [A]; linarith
  have hB : 0 ≤ B := by have H := hs.2 b hb; dsimp [B]; linarith
  have hinner_sum : inner ℝ s (a - c) + inner ℝ s (b - c) = 0 := by
    rw [← inner_add_right]
    have H : a - c + (b - c) = 0 := by dsimp [c]; module
    rw [H, inner_zero_right]
  have hAB : A + B = 2 * ((r.value a + r.value b) / 2 - r.value c) := by
    dsimp [A, B]
    linarith only [hinner_sum]
  have hcv := hr.2.2.2 ha hb hα hβ hsum
  have hlinear : inner ℝ s (α • a + β • b - c) =
      α * inner ℝ s (a - c) + β * inner ℝ s (b - c) := by
    have H : α • a + β • b - c = α • (a - c) + β • (b - c) := by
      calc
        α • a + β • b - c = α • a + β • b - (α + β) • c := by rw [hsum, one_smul]
        _ = α • (a - c) + β • (b - c) := by module
    rw [H, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hgap_lower : 0 ≤ r.value (c + (δ * t) • v) - r.value c - δ * t * inner ℝ s v := by
    have H := hs.2 _ hdom
    rw [add_sub_cancel_left, real_inner_smul_right] at H
    linarith
  have hgap_upper : r.value (c + (δ * t) • v) - r.value c - δ * t * inner ℝ s v ≤ A + B := by
    have hi : δ * t * inner ℝ s v = inner ℝ s (α • a + β • b - c) := by
      calc
        δ * t * inner ℝ s v = inner ℝ s ((δ * t) • v) := by simp only [real_inner_smul_right]
        _ = inner ℝ s (α • a + β • b - c) := by rw [← heq, add_sub_cancel_left]
    rw [heq, hi, hlinear]
    have hAA := mul_le_mul_of_nonneg_right hα1 hA
    have hBB := mul_le_mul_of_nonneg_right hβ1 hB
    dsimp [A, B] at hAA hBB
    simp only [smul_eq_mul] at hcv
    have hconst : α * r.value c + β * r.value c = r.value c := by rw [← add_mul, hsum, one_mul]
    dsimp [A, B]
    nlinarith only [hcv, hAA, hBB, hconst]
  have hbound : A + B ≤ ε * δ ^ 2 := by
    rw [hAB]
    have hnorm : ‖a - b‖ ^ 2 = D ^ 2 := by dsimp [D]; rw [norm_sub_rev]
    rw [hnorm] at hgap
    have halg : 2 * η * D ^ 2 = ε * δ ^ 2 := by
      dsimp [η, δ]
      field_simp [ne_of_gt hM]
      <;> ring
    dsimp [c] at hAB
    have H : 2 * ((r.value a + r.value b) / 2 - r.value c) < 2 * η * D ^ 2 := by
      dsimp [c]
      linarith only [hgap]
    linarith only [H, halg]
  refine ⟨hdom, div_nonneg hgap_lower (sq_nonneg δ), ?_⟩
  apply (div_le_iff₀ (sq_pos_of_pos hδ)).2
  exact hgap_upper.trans hbound
