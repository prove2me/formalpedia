-- Prove2me | solution 1 for OneEdgeEndpointSectorComplementPackage
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T03:49:25.193421+00:00
-- url     : https://prove2.me/submissions/b98aa499-5474-4acc-9c33-caed4367cf87

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Classical
noncomputable section

lemma solution
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2)
    (hEdgeSource :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ∈ V)
    (hEdgeTarget :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.2 ∈ V)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (hpV : p ∈ V) (hqV : q ∈ V)
    (hpq : p ≠ q)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ p q) A)
    (r : ℝ) (hr_pos : 0 < r)
    (hr_vertices :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ p → v ∉ Metric.ball p r)
    (hr_nonincident_edges :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ p → e.2 ≠ p →
          Disjoint (Metric.ball p r) (segment ℝ e.1 e.2)) :
    let Incident :=
      {e : {e // e ∈ E} // e.1.1 = p ∨ e.1.2 = p}
    let u : Option Incident → EuclideanSpace ℝ (Fin 2) :=
      fun i =>
        match i with
        | none => q - p
        | some e =>
            if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p
    ∃ clockwiseNext : Equiv.Perm (Option Incident),
      ∃ fullClockwiseTurn : ℝ,
      ∃ clockwiseTurn : Option Incident → Option Incident → ℝ,
      ∃ sector : Option Incident → Set (EuclideanSpace ℝ (Fin 2)),
        fullClockwiseTurn = 2 * Real.pi ∧
        0 < fullClockwiseTurn ∧
        (∀ i j : Option Incident, 0 < clockwiseTurn i j) ∧
        (∀ i j : Option Incident, clockwiseTurn i j ≤ fullClockwiseTurn) ∧
        (∀ i j : Option Incident, clockwiseTurn i j = fullClockwiseTurn ↔ j = i) ∧
        (∀ i j : Option Incident, j ≠ i →
          clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
        (∀ i : Option Incident,
          clockwiseNext i = i ↔ ∀ j : Option Incident, j = i) ∧
        (∀ i : Option Incident,
          IsOpen (sector i) ∧
            IsConnected (sector i) ∧
            sector i ⊆ Metric.ball p r ∧
            sector i ⊆ (A ∪ segment ℝ p q)ᶜ) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ Metric.ball p r → x ∈ A → x ≠ p →
            ∃ i : Incident, ∃ t : ℝ, 0 < t ∧ x = p + t • u (some i)) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ segment ℝ p q → x ≠ p →
            ∃ t : ℝ, 0 < t ∧ x = p + t • u none) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ Metric.ball p r → x ∈ (A ∪ segment ℝ p q)ᶜ →
            ∃ i : Option Incident, x ∈ sector i) := by
  intro Incident u
  classical
  have hpA : p ∈ A := by rw [hA]; exact Or.inl hpV
  have hsegA : ∀ e ∈ E, segment ℝ e.1 e.2 ⊆ A := by
    intro e he x hx; rw [hA]; exact Or.inr (Set.mem_iUnion.mpr ⟨⟨e, he⟩, hx⟩)
  have hu : ∀ i, ∃ v, u i = v - p ∧ v ∈ V ∧ v ≠ p ∧ segment ℝ p v ⊆ A ∪ segment ℝ p q := by
    intro i
    rcases i with _ | ⟨⟨e, he⟩, hinc⟩
    · exact ⟨q, rfl, hqV, hpq.symm, Set.subset_union_right⟩
    · by_cases h1 : e.1 = p
      · refine ⟨e.2, by simp [u, h1], hEdgeTarget e he, ?_, ?_⟩
        · intro h2; exact hEdgeNondegenerate e he (h1.trans h2.symm)
        · intro x hx; left; apply hsegA e he; rw [h1]; exact hx
      · refine ⟨e.1, by simp [u, h1], hEdgeSource e he, h1, ?_⟩
        have h2 : e.2 = p := hinc.resolve_left h1
        intro x hx; left; apply hsegA e he; rw [h2, segment_symm]; exact hx
  have hu_norm : ∀ i, r ≤ ‖u i‖ := by
    intro i
    obtain ⟨v, hv, hvV, hvp, -⟩ := hu i
    have := hr_vertices v hvV hvp
    rw [Metric.mem_ball, not_lt, dist_eq_norm] at this
    rwa [hv]
  have hu_ne : ∀ i, u i ≠ 0 := by
    intro i h0; have := hu_norm i; rw [h0, norm_zero] at this; linarith
  have hRayConv : ∀ i x (t : ℝ), 0 ≤ t → x = p + t • u i → x ∈ Metric.ball p r →
      x ∈ A ∪ segment ℝ p q := by
    intro i x t ht hx hxb
    obtain ⟨v, hv, -, -, hsub⟩ := hu i
    have hn := hu_norm i
    rw [Metric.mem_ball, dist_eq_norm, hx, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht] at hxb
    have ht1 : t < 1 := by
      by_contra hh; push_neg at hh; nlinarith
    apply hsub
    rw [segment_eq_image']
    exact ⟨t, ⟨ht, ht1.le⟩, by rw [hx, hv]⟩
  have hA_ray : ∀ x : EuclideanSpace ℝ (Fin 2),
      x ∈ Metric.ball p r → x ∈ A → x ≠ p →
        ∃ i : Incident, ∃ t : ℝ, 0 < t ∧ x = p + t • u (some i) := by
    intro x hxb hxA hxp
    rw [hA] at hxA
    rcases hxA with hxV | hxE
    · exact absurd hxb (hr_vertices x hxV hxp)
    · obtain ⟨⟨e, he⟩, hx⟩ := Set.mem_iUnion.mp hxE
      by_cases h1 : e.1 = p
      · refine ⟨⟨⟨e, he⟩, Or.inl h1⟩, ?_⟩
        rw [segment_eq_image', h1] at hx
        obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
        refine ⟨t, ?_, by simp [u, h1]⟩
        rcases ht0.lt_or_eq with h | h
        · exact h
        · exfalso; apply hxp; rw [← h]; simp
      · by_cases h2 : e.2 = p
        · refine ⟨⟨⟨e, he⟩, Or.inr h2⟩, ?_⟩
          rw [segment_symm, segment_eq_image', h2] at hx
          obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
          refine ⟨t, ?_, by simp [u, h1]⟩
          rcases ht0.lt_or_eq with h | h
          · exact h
          · exfalso; apply hxp; rw [← h]; simp
        · exact absurd hx (Set.disjoint_left.mp (hr_nonincident_edges e he h1 h2) hxb)
  have hQ_ray : ∀ x : EuclideanSpace ℝ (Fin 2),
      x ∈ segment ℝ p q → x ≠ p → ∃ t : ℝ, 0 < t ∧ x = p + t • u none := by
    intro x hx hxp
    rw [segment_eq_image'] at hx
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
    refine ⟨t, ?_, rfl⟩
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hxp; rw [← h]; simp
  have hRay : ∀ x, x ∈ Metric.ball p r → x ∈ A ∪ segment ℝ p q → x ≠ p →
      ∃ j, ∃ t : ℝ, 0 < t ∧ x = p + t • u j := by
    intro x hxb hx hxp
    rcases hx with hx | hx
    · obtain ⟨i, t, ht, h⟩ := hA_ray x hxb hx hxp
      exact ⟨some i, t, ht, h⟩
    · obtain ⟨t, ht, h⟩ := hQ_ray x hx hxp
      exact ⟨none, t, ht, h⟩
  -- complex coordinates
  let L : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let a : Option Incident → ℂ := fun i => L (u i)
  have ha_ne : ∀ i, a i ≠ 0 := fun i => by
    simp only [a, ne_eq, LinearIsometryEquiv.map_eq_zero_iff]; exact hu_ne i
  have ha_npos : ∀ i, 0 < ‖a i‖ := fun i => norm_pos_iff.mpr (ha_ne i)
  let f : Option Incident → EuclideanSpace ℝ (Fin 2) → ℂ :=
    fun i x => -(L (x - p) * (starRingEnd ℂ) (a i))
  have hf_cont : ∀ i, Continuous (f i) := fun i =>
    ((L.continuous.comp (continuous_id.sub continuous_const)).mul continuous_const).neg
  let c : Option Incident → Option Incident → ℂ := fun i j => -(a j * (starRingEnd ℂ) (a i))
  let h : Option Incident → Option Incident → ℝ := fun i j =>
    if c i j ∈ Complex.slitPlane then Complex.arg (c i j) + Real.pi else 2 * Real.pi
  let g : Option Incident → ℝ := fun i => ⨅ j, h i j
  have hh_bd : ∀ i j, 0 < h i j ∧ h i j ≤ 2 * Real.pi := by
    intro i j
    simp only [h]
    split_ifs
    · constructor
      · linarith [Complex.neg_pi_lt_arg (c i j)]
      · linarith [Complex.arg_le_pi (c i j)]
    · constructor
      · linarith [Real.pi_pos]
      · rfl
  have hg_le : ∀ i j, g i ≤ h i j := fun i j => ciInf_le (Finite.bddBelow_range _) j
  have hg : ∀ i, 0 < g i ∧ g i ≤ 2 * Real.pi := by
    intro i
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := h i)
    show 0 < ⨅ j, h i j ∧ (⨅ j, h i j) ≤ 2 * Real.pi
    rw [← hj]; exact hh_bd i j
  let sector : Option Incident → Set (EuclideanSpace ℝ (Fin 2)) := fun i =>
    {x | x ∈ Metric.ball p r ∧ f i x ∈ Complex.slitPlane ∧
      Complex.arg (f i x) < g i - Real.pi}
  have K1 : ∀ i x, x ∈ Metric.ball p r → f i x ∉ Complex.slitPlane →
      x ∈ A ∪ segment ℝ p q := by
    intro i x hxb hns
    rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hns
    obtain ⟨hre, him⟩ := hns
    have hre' : 0 ≤ (L (x - p) * (starRingEnd ℂ) (a i)).re := by
      simp only [f, Complex.neg_re] at hre; linarith
    have him' : (L (x - p) * (starRingEnd ℂ) (a i)).im = 0 := by
      simp only [f, Complex.neg_im] at him; linarith
    have hwr : L (x - p) * (starRingEnd ℂ) (a i) =
        ((L (x - p) * (starRingEnd ℂ) (a i)).re : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]) (by rw [Complex.ofReal_im]; exact him')
    set w := (L (x - p) * (starRingEnd ℂ) (a i)).re with hw
    have hz : L (x - p) = ((w / ‖a i‖ ^ 2 : ℝ) : ℂ) * a i := by
      have h1 := Complex.mul_conj' (a i)
      have hn : (‖a i‖ : ℂ) ≠ 0 := by exact_mod_cast (ha_npos i).ne'
      push_cast
      field_simp
      linear_combination (-(L (x - p))) * h1 + a i * hwr
    have hxt : x = p + (w / ‖a i‖ ^ 2) • u i := by
      have : x - p = (w / ‖a i‖ ^ 2) • u i := by
        apply L.injective
        rw [map_smul, Complex.real_smul]; exact hz
      rw [← this]; abel
    exact hRayConv i x _ (div_nonneg hre' (by positivity)) hxt hxb
  have K2 : ∀ i x, x ∈ sector i → x ∉ A ∪ segment ℝ p q := by
    rintro i x ⟨hxb, hslit, harg⟩ hxA
    have hxp : x ≠ p := by
      rintro rfl; apply Complex.slitPlane_ne_zero hslit; simp [f]
    obtain ⟨j, t, ht, rfl⟩ := hRay _ hxb hxA hxp
    have hfx : f i (p + t • u j) = (t : ℂ) * c i j := by
      simp only [f, c, a, add_sub_cancel_left, map_smul, Complex.real_smul]; ring
    rw [hfx] at hslit harg
    have hc : c i j ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hslit ⊢
      rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul] at hslit
      rcases hslit with hh | hh
      · left; by_contra hh'; push_neg at hh'; nlinarith
      · right; intro h0; apply hh; rw [h0, mul_zero]
    rw [Complex.arg_real_mul _ ht] at harg
    have := hg_le i j
    simp only [h, if_pos hc] at this
    linarith
  have K3 : ∀ x ∈ Metric.ball p r, x ∈ (A ∪ segment ℝ p q)ᶜ → ∃ i, x ∈ sector i := by
    intro x hxb hxc
    have hslit : ∀ j, f j x ∈ Complex.slitPlane := fun j => by
      by_contra hh; exact hxc (K1 j x hxb hh)
    obtain ⟨i, hi⟩ := Finite.exists_min (fun j => Complex.arg (f j x))
    refine ⟨i, hxb, hslit i, ?_⟩
    obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := h i)
    show Complex.arg (f i x) < (⨅ j, h i j) - Real.pi
    rw [← hj]
    simp only [h]
    split_ifs with hc
    · by_contra hge; push_neg at hge
      have hfi0 := Complex.slitPlane_ne_zero (hslit i)
      have hfj0 := Complex.slitPlane_ne_zero (hslit j)
      have hc0 := Complex.slitPlane_ne_zero hc
      have hN : 0 < ‖a j‖ ^ 2 := by have := ha_npos j; positivity
      have key : f j x * c i j = -(((‖a j‖ ^ 2 : ℝ) : ℂ) * f i x) := by
        simp only [f, c]; push_cast; rw [← Complex.mul_conj']; ring
      have hang := Complex.arg_mul_coe_angle hfj0 hc0
      rw [key, Complex.arg_neg_coe_angle (mul_ne_zero (by exact_mod_cast hN.ne') hfi0),
        Complex.arg_real_mul _ hN, ← Real.Angle.coe_add, ← Real.Angle.coe_add,
        Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hang
      obtain ⟨k, hk⟩ := hang
      have h1 := hi j
      have h2 : Complex.arg (f j x) < Real.pi :=
        Complex.arg_lt_pi_iff.mpr (by
          rcases Complex.mem_slitPlane_iff.mp (hslit j) with hh | hh
          · exact Or.inl hh.le
          · exact Or.inr hh)
      have h3 := Complex.neg_pi_lt_arg (c i j)

      have hk0 : (0:ℝ) < k := by
        by_contra hh; push_neg at hh; nlinarith [Real.pi_pos]
      have hk1 : (k:ℝ) < 1 := by
        by_contra hh; push_neg at hh; nlinarith [Real.pi_pos]
      have : (0:ℤ) < k := by exact_mod_cast hk0
      have : k < 1 := by exact_mod_cast hk1
      omega
    · have := Complex.arg_lt_pi_iff.mpr (by
          rcases Complex.mem_slitPlane_iff.mp (hslit i) with hh | hh
          · exact Or.inl hh.le
          · exact Or.inr hh)
      linarith
  have hopen : ∀ i, IsOpen (sector i) := by
    intro i
    have hs : IsOpen (Metric.ball p r ∩ f i ⁻¹' Complex.slitPlane) :=
      Metric.isOpen_ball.inter (Complex.isOpen_slitPlane.preimage (hf_cont i))
    have hco : ContinuousOn (fun x => Complex.arg (f i x))
        (Metric.ball p r ∩ f i ⁻¹' Complex.slitPlane) := fun x hx =>
      ((Complex.continuousAt_arg hx.2).comp (hf_cont i).continuousAt).continuousWithinAt
    have := hco.isOpen_inter_preimage hs (isOpen_Iio (a := g i - Real.pi))
    convert this using 1
    ext x; simp only [sector, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Iio, and_assoc]
  have hconn : ∀ i, IsConnected (sector i) := by
    intro i
    let Φ : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) := fun st =>
      p + L.symm (-(((st.1 / ‖a i‖ : ℝ) : ℂ) *
        (Complex.cos (st.2 : ℂ) + Complex.sin (st.2 : ℂ) * Complex.I) * a i))
    have hΦ : Continuous Φ := continuous_const.add (L.symm.continuous.comp (by fun_prop))
    have heq : sector i = Φ '' (Set.Ioo 0 r ×ˢ Set.Ioo (-Real.pi) (g i - Real.pi)) := by
      ext x; constructor
      · rintro ⟨hxb, hslit, harg⟩
        have hw0 := Complex.slitPlane_ne_zero hslit
        have hxp : x ≠ p := by rintro rfl; apply hw0; simp [f]
        refine ⟨(‖x - p‖, Complex.arg (f i x)),
          ⟨⟨norm_pos_iff.mpr (sub_ne_zero.mpr hxp), by rwa [Metric.mem_ball, dist_eq_norm] at hxb⟩,
            Complex.neg_pi_lt_arg _, harg⟩, ?_⟩
        have hY : -((((‖x - p‖ / ‖a i‖ : ℝ) : ℂ) *
            (Complex.cos ((Complex.arg (f i x) : ℝ) : ℂ) +
              Complex.sin ((Complex.arg (f i x) : ℝ) : ℂ) * Complex.I) * a i)) = L (x - p) := by
          have hpol := Complex.norm_mul_cos_add_sin_mul_I (f i x)
          have hnf : ‖f i x‖ = ‖x - p‖ * ‖a i‖ := by
            simp only [f, norm_neg, norm_mul, Complex.norm_conj, LinearIsometryEquiv.norm_map]
          rw [hnf] at hpol
          have h1 := Complex.mul_conj' (a i)
          have hn : (‖a i‖ : ℂ) ≠ 0 := by exact_mod_cast (ha_npos i).ne'
          have hfx : f i x = -(L (x - p) * (starRingEnd ℂ) (a i)) := rfl
          push_cast at hpol ⊢
          field_simp
          apply mul_left_cancel₀ hn
          linear_combination (-(a i)) * hpol - (a i) * hfx + (L (x - p)) * h1
        simp only [Φ]
        rw [hY, LinearIsometryEquiv.symm_apply_apply]; abel
      · rintro ⟨⟨s, θ⟩, ⟨⟨hs0, hsr⟩, hθ1, hθ2⟩, rfl⟩
        have hθ3 : θ < Real.pi := by linarith [(hg i).2]
        have hfΦ : f i (Φ (s, θ)) = ((s * ‖a i‖ : ℝ) : ℂ) *
            (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) := by
          have h1 := Complex.mul_conj' (a i)
          have hn : (‖a i‖ : ℂ) ≠ 0 := by exact_mod_cast (ha_npos i).ne'
          simp only [f, Φ, add_sub_cancel_left, LinearIsometryEquiv.apply_symm_apply]
          push_cast
          field_simp
          linear_combination ((s : ℂ)) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) * h1
        have hsn : 0 < s * ‖a i‖ := mul_pos hs0 (ha_npos i)
        have harg : Complex.arg (f i (Φ (s, θ))) = θ := by
          rw [hfΦ]; exact Complex.arg_mul_cos_add_sin_mul_I hsn ⟨hθ1, hθ3.le⟩
        refine ⟨?_, ?_, by rw [harg]; exact hθ2⟩
        · rw [Metric.mem_ball, dist_eq_norm]
          have hnf : ‖f i (Φ (s, θ))‖ = ‖Φ (s, θ) - p‖ * ‖a i‖ := by
            simp only [f, norm_neg, norm_mul, Complex.norm_conj, LinearIsometryEquiv.norm_map]
          rw [hfΦ, norm_mul, Complex.norm_cos_add_sin_mul_I, Complex.norm_real,
            Real.norm_of_nonneg hsn.le, mul_one] at hnf
          have : ‖Φ (s, θ) - p‖ = s := by
            exact (mul_right_cancel₀ (ha_npos i).ne' hnf).symm
          rw [this]; exact hsr
        · rw [Complex.mem_slitPlane_iff_arg, harg]
          refine ⟨hθ3.ne, ?_⟩
          rw [hfΦ]
          refine mul_ne_zero (by exact_mod_cast hsn.ne') ?_
          intro h0
          have := Complex.norm_cos_add_sin_mul_I θ
          rw [h0, norm_zero] at this; exact zero_ne_one this
    rw [heq]
    exact ((isConnected_Ioo hr_pos).prod (isConnected_Ioo (by linarith [(hg i).1]))).image _
      hΦ.continuousOn
  have hperm : ∃ σ : Equiv.Perm (Option Incident), ∀ i, σ i = i ↔ ∀ j : Option Incident, j = i := by
    obtain ⟨n, ⟨eqv⟩⟩ : ∃ n, Nonempty (Option Incident ≃ Fin n) := ⟨_, ⟨Fintype.equivFin _⟩⟩
    match n, eqv with
    | 0, eqv => exact (eqv none).elim0
    | 1, eqv => exact ⟨1, fun i => ⟨fun _ j => eqv.injective (Subsingleton.elim _ _), fun _ => rfl⟩⟩
    | m + 2, eqv =>
      refine ⟨eqv.symm.permCongr (finRotate (m + 2)), fun i => ⟨fun hfix => ?_, fun hall => ?_⟩⟩
      · exfalso
        have hne : finRotate (m + 2) (eqv i) ≠ eqv i :=
          Equiv.Perm.mem_support.mp (by simp [support_finRotate])
        apply hne
        rw [Equiv.permCongr_apply] at hfix
        simpa using congrArg eqv hfix
      · exfalso
        have h0 := hall (eqv.symm 0)
        have h1 := hall (eqv.symm 1)
        have := eqv.symm.injective (h0.trans h1.symm)
        simp at this
  obtain ⟨σ, hσ⟩ := hperm
  refine ⟨σ, 2 * Real.pi, fun i j => if j = i then 2 * Real.pi else Real.pi, sector, rfl,
    by positivity, ?_, ?_, ?_, ?_, hσ, ?_, hA_ray, hQ_ray, K3⟩
  · intro i j; dsimp only; split_ifs <;> positivity
  · intro i j; dsimp only; split_ifs <;> linarith [Real.pi_pos]
  · intro i j; dsimp only; split_ifs with hji
    · simp [hji]
    · simp only [hji, iff_false]; intro h0; linarith [Real.pi_pos]
  · intro i j hji
    dsimp only
    have hσi : σ i ≠ i := fun hfix => hji ((hσ i).mp hfix j)
    rw [if_neg hσi, if_neg hji]
  · intro i
    exact ⟨hopen i, hconn i, fun x hx => hx.1, fun x hx => K2 i x hx⟩
