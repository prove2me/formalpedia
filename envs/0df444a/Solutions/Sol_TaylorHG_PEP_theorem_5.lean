-- Prove2me | solution 1 for TaylorHG.PEP.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T00:29:16.201495+00:00
-- url     : https://prove2.me/submissions/4bb11d56-11cd-448d-9bce-dede88f880b0

import Mathlib
import Definitions.Def_TaylorHG_PEP_SDP
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof
end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof
open ShorNonsmooth.AlmostDiff

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem quadratic_remainder_gradient {f : E → ℝ} {x g : E} {C : ℝ}
    (h : ∀ v, 0 ≤ f (x + v) - f x - inner ℝ g v ∧
      f (x + v) - f x - inner ℝ g v ≤ C * ‖v‖ ^ 2) :
    HasGradientAt f g x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have hb : (fun v : E => f (x + v) - f x - inner ℝ g v) =O[𝓝 0]
      (fun v : E => ‖v‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [] with v
    simpa only [Real.norm_eq_abs, abs_of_nonneg (h v).1,
      abs_of_nonneg (sq_nonneg ‖v‖)] using (h v).2
  exact hb.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))

theorem exists_subgradient {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x : E) :
    ∃ g : E, IsSubgradient f x g := by
  have hc : Continuous f := continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  let epi : Set (E × ℝ) := {p | f p.1 < p.2}
  have hec : Convex ℝ epi := by
    simpa only [Set.mem_univ, true_and] using hf.convex_strict_epigraph
  have heo : IsOpen epi := isOpen_lt (hc.comp continuous_fst) continuous_snd
  obtain ⟨ell, hell⟩ := geometric_hahn_banach_point_open hec heo
    (show (x, f x) ∉ epi by simp [epi])
  let u : StrongDual ℝ E := ell.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let c : ℝ := ell (0, 1)
  have split (y : E) (t : ℝ) : ell (y, t) = u y + c * t := by
    have he : (y, t) = (y, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by ext <;> simp
    rw [he, map_add, map_smul]
    simp [u, c, mul_comm]
  have cp : 0 < c := by
    have hh := hell (x, f x + 1) (by dsimp [epi]; linarith)
    rw [split, split] at hh
    linarith
  let v : StrongDual ℝ E := (-c⁻¹) • u
  refine ⟨(InnerProductSpace.toDual ℝ E).symm v, ?_⟩
  intro y
  rw [InnerProductSpace.toDual_symm_apply]
  have hb : u x + c * f x ≤ u y + c * f y := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hh := hell (y, f y + ε / c) (by dsimp [epi]; exact lt_add_of_pos_right _ (div_pos hε cp))
    rw [split, split] at hh
    have he : c * (f y + ε / c) = c * f y + ε := by field_simp
    rw [he] at hh
    simpa only [add_assoc] using hh.le
  have hu : u (y - x) = u y - u x := map_sub u y x
  change -(c⁻¹) * u (y - x) ≤ f y - f x
  rw [hu]
  apply (mul_le_mul_iff_right₀ cp).mp
  field_simp
  nlinarith

theorem subgradient_eq_gradient {f : E → ℝ} {x g g' : E}
    (hs : IsSubgradient f x g) (hg : HasGradientAt f g' x) : g = g' := by
  let q : E → ℝ := fun y => f y - inner ℝ g y
  have hmin : IsMinOn q Set.univ x := by
    intro y _
    have h := hs y
    dsimp [q]
    rw [inner_sub_right] at h
    linarith
  have hq : HasFDerivAt q
      (InnerProductSpace.toDual ℝ E g' - InnerProductSpace.toDual ℝ E g) x :=
    hg.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E g).hasFDerivAt
  have he := (hmin.isLocalMin (by simp)).hasFDerivAt_eq_zero hq
  exact ((InnerProductSpace.toDual ℝ E).injective (sub_eq_zero.mp he)).symm

theorem gradient_subgradient {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f)
    {x g : E} (hg : HasGradientAt f g x) : IsSubgradient f x g := by
  obtain ⟨g', hs⟩ := exists_subgradient hf x
  rwa [subgradient_eq_gradient hs hg] at hs

theorem gradient_unique {f : E → ℝ} {x g : E} (hg : HasGradientAt f g x) :
    gradient f x = g := hg.gradient

theorem quadratic_hasGradient (μ : ℝ) (x : E) :
    HasGradientAt (fun y : E => μ / 2 * ‖y‖ ^ 2) (μ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have he : InnerProductSpace.toDual ℝ E (μ • x) =
      (μ / 2) • (2 • innerSL ℝ x) := by
    ext v
    simp only [InnerProductSpace.toDual_apply_apply, smul_apply, innerSL_apply_apply,
      smul_eq_mul, real_inner_smul_left]
    ring
  rw [he]
  exact (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ / 2)

end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof
open ShorNonsmooth.AlmostDiff TaylorHG.PEP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem native_subgradient_lipschitz {μ L : NNReal} (hL : 0 < L) {f : E → ℝ}
    (hf : FClass μ (L : ENNReal) f) {x y g q : E}
    (hx : IsSubgradient f x g) (hy : IsSubgradient f y q) :
    ‖g - q‖ ≤ (L : ℝ) * ‖x - y‖ := by
  have h := hf.2.1 x y g q hx hy
  simp only [ENNReal.toReal_inv, ENNReal.coe_toReal] at h
  have hp : 0 < (L : ℝ) := hL
  have hh := mul_le_mul_of_nonneg_left h hp.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] using hh

theorem fclass_hasGradient {μ L : NNReal} (hL : 0 < L) {f : E → ℝ}
    (hf : FClass μ (L : ENNReal) f) (x : E) :
    HasGradientAt f (gradient f x) x ∧ IsSubgradient f x (gradient f x) := by
  obtain ⟨g, hg⟩ := exists_subgradient hf.1 x
  have hd : HasGradientAt f g x := by
    apply quadratic_remainder_gradient (C := (L : ℝ))
    intro v
    obtain ⟨q, hq⟩ := exists_subgradient hf.1 (x + v)
    have ha := hg (x + v)
    have hb := hq x
    have hl := native_subgradient_lipschitz hL hf hq hg
    have hi := real_inner_le_norm (q - g) v
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg v)
    simp only [add_sub_cancel_left] at ha hl hm
    have he : x - (x + v) = -v := by abel
    rw [he, inner_neg_right] at hb
    rw [inner_sub_left] at hi
    constructor
    · linarith
    · nlinarith
  exact ⟨by simpa only [hd.gradient] using hd, by simpa only [hd.gradient] using hg⟩

theorem fclass_gradient_lipschitz {μ L : NNReal} (hL : 0 < L) {f : E → ℝ}
    (hf : FClass μ (L : ENNReal) f) (x y : E) :
    ‖gradient f x - gradient f y‖ ≤ (L : ℝ) * ‖x - y‖ :=
  native_subgradient_lipschitz hL hf (fclass_hasGradient hL hf x).2
    (fclass_hasGradient hL hf y).2

theorem gradient_upper_model {f : E → ℝ} {g : E → E} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + inner ℝ (g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  let v := y - x
  let q : ℝ → ℝ := fun t => f (x + t • v) - f x -
    t * inner ℝ (g x) v - (L / 2) * t ^ 2 * ‖v‖ ^ 2
  let q' : ℝ → ℝ := fun t => inner ℝ (g (x + t • v)) v -
    inner ℝ (g x) v - L * t * ‖v‖ ^ 2
  have hd (t : ℝ) : HasDerivAt q (q' t) t := by
    have ht : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hh := (hg (x + t • v)).hasFDerivAt.comp_hasDerivAt t ht
    have hh' : HasDerivAt (fun t : ℝ => f (x + t • v))
        (inner ℝ (g (x + t • v)) v) t := by
      simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hh
    convert! (((hh'.sub_const (f x)).sub ((hasDerivAt_id t).mul_const _)).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖v‖ ^ 2))) using 1
    dsimp [q']
    ring
  have hn (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) : q' t ≤ 0 := by
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hl := hlip (x + t • v) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0] at hl
    have hi := real_inner_le_norm (g (x + t • v) - g x) v
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg v)
    rw [inner_sub_left] at hi
    dsimp [q']
    nlinarith
  have ha : AntitoneOn q (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt) hn
  have h := ha (by simp) (by simp) (by norm_num : (0 : ℝ) ≤ 1)
  simp [q, v] at h
  linarith

end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof
open ShorNonsmooth.AlmostDiff TaylorHG.PEP
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem shifted_pairwise {f : E → ℝ} {g : E → E} {M : ℝ} (hM : 0 < M)
    (hs : ∀ x, IsSubgradient f x (g x))
    (hu : ∀ x y, f y ≤ f x + inner ℝ (g x) (y - x) + M / 2 * ‖y - x‖ ^ 2)
    (x y : E) : ‖g x - g y‖ ^ 2 / (2 * M) ≤
      f x - f y - inner ℝ (g y) (x - y) := by
  let u := g x - g y
  let v := -M⁻¹ • u
  have hh := hu x (x + v)
  have hl := hs y (x + v)
  have hdiff : x + v - y = (x - y) + v := by abel
  simp only [add_sub_cancel_left] at hh
  rw [hdiff, inner_add_right] at hl
  have hi : inner ℝ (g x) v + M / 2 * ‖v‖ ^ 2 - inner ℝ (g y) v =
      -‖u‖ ^ 2 / (2 * M) := by
    have hi' : inner ℝ (g x) u - inner ℝ (g y) u = ‖u‖ ^ 2 := by
      rw [← inner_sub_left]
      exact real_inner_self_eq_norm_sq u
    dsimp [v]
    rw [inner_smul_right, inner_smul_right, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
    field_simp
    nlinarith
  dsimp [u] at hi
  rw [neg_div] at hi
  linarith

theorem fclass_shifted_pairwise {μ L : NNReal} (hμL : μ < L) {f : E → ℝ}
    (hf : FClass μ (L : ENNReal) f) (x y : E) :
    ‖(gradient f x - (μ : ℝ) • x) - (gradient f y - (μ : ℝ) • y)‖ ^ 2 /
      (2 * ((L : ℝ) - (μ : ℝ))) ≤
    (f x - (μ : ℝ) / 2 * ‖x‖ ^ 2) - (f y - (μ : ℝ) / 2 * ‖y‖ ^ 2) -
      inner ℝ (gradient f y - (μ : ℝ) • y) (x - y) := by
  have hL : 0 < L := lt_of_le_of_lt (zero_le : (0 : NNReal) ≤ μ) hμL
  let a : E → ℝ := fun z => f z - (μ : ℝ) / 2 * ‖z‖ ^ 2
  let s : E → E := fun z => gradient f z - (μ : ℝ) • z
  have ha : ∀ z, HasGradientAt a (s z) z := by
    intro z
    rw [hasGradientAt_iff_hasFDerivAt]
    dsimp [a, s]
    rw [map_sub]
    exact (fclass_hasGradient hL hf z).1.hasFDerivAt.sub (quadratic_hasGradient (μ : ℝ) z).hasFDerivAt
  apply shifted_pairwise (show 0 < (L : ℝ) - (μ : ℝ) by exact sub_pos.mpr hμL)
    (fun z => gradient_subgradient hf.2.2 (ha z))
  intro u v
  have hu := gradient_upper_model (fun z => (fclass_hasGradient hL hf z).1)
    (fclass_gradient_lipschitz hL hf) u v
  have hn := norm_add_sq_real u (v - u)
  have he : u + (v - u) = v := by abel
  rw [he] at hn
  dsimp [a, s]
  rw [inner_sub_left, real_inner_smul_left]
  nlinarith

end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem strong_min_gap {h : E → ℝ} {c : ℝ} {p : E}
    (hc : ConvexOn ℝ Set.univ (fun z => h z - c * ‖z‖ ^ 2))
    (hp : ∀ z, h p ≤ h z) (z : E) :
    h p + c * ‖z - p‖ ^ 2 ≤ h z := by
  have hs : StrongConvexOn Set.univ (2 * c) h := by
    apply strongConvexOn_iff_convex.mpr
    simpa using hc
  have hb (n : ℕ) : (1 - 1 / ((n : ℝ) + 1)) * c * ‖z - p‖ ^ 2 ≤ h z - h p := by
    let t : ℝ := 1 / ((n : ℝ) + 1)
    have ht : 0 < t := by dsimp [t]; positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]
      apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hh := hs.2 (Set.mem_univ p) (Set.mem_univ z)
      (sub_nonneg.mpr ht1) ht.le (by ring : (1 - t) + t = 1)
    have hm := hp ((1 - t) • p + t • z)
    simp only [smul_eq_mul] at hh
    rw [norm_sub_rev p z] at hh
    have he : (2 * c) / 2 = c := by ring
    rw [he] at hh
    have hx : t * ((1 - t) * c * ‖z - p‖ ^ 2) ≤ t * (h z - h p) := by
      nlinarith
    exact (mul_le_mul_iff_right₀ ht).mp hx
  have hl : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 1)) * c * ‖z - p‖ ^ 2)
      atTop (𝓝 (c * ‖z - p‖ ^ 2)) := by
    convert ((tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat).mul_const c).mul_const
      (‖z - p‖ ^ 2) using 1; norm_num
  have hh := le_of_tendsto hl (Filter.Eventually.of_forall hb)
  linarith

theorem strong_linear_min_gap {h : E → ℝ} {c : ℝ} {p x : E}
    (hc : ConvexOn ℝ Set.univ (fun z => h z - c * ‖z‖ ^ 2))
    (hp : ∀ z, h p - inner ℝ x p ≤ h z - inner ℝ x z) (z : E) :
    h p - inner ℝ x p + c * ‖z - p‖ ^ 2 ≤ h z - inner ℝ x z := by
  apply strong_min_gap (h := fun y => h y - inner ℝ x y) (p := p) ?_ hp z
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ u v hu hv huv
  have hh := hc.2 (Set.mem_univ a) (Set.mem_univ b) hu hv huv
  simp only [inner_add_right, inner_smul_right, smul_eq_mul] at hh ⊢
  linarith

end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ (Fin d)

def quadraticEnvelope (c : ℝ) (x s : ι → E) (a : ι → ℝ) (z : E) : ℝ :=
  c * ‖z‖ ^ 2 + Finset.univ.sup' Finset.univ_nonempty
    (fun i => inner ℝ (x i - (2 * c) • s i) z + c * ‖s i‖ ^ 2 - a i)

theorem quadraticEnvelope_continuous (c : ℝ) (x s : ι → E) (a : ι → ℝ) :
    Continuous (quadraticEnvelope c x s a) := by
  unfold quadraticEnvelope
  apply Continuous.add (by fun_prop)
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => by fun_prop)

theorem quadraticEnvelope_shift_convex (c : ℝ) (x s : ι → E) (a : ι → ℝ) :
    ConvexOn ℝ Set.univ (fun z => quadraticEnvelope c x s a z - c * ‖z‖ ^ 2) := by
  have hc : ConvexOn ℝ Set.univ (fun z => Finset.univ.sup' Finset.univ_nonempty
      (fun i => inner ℝ (x i - (2 * c) • s i) z + c * ‖s i‖ ^ 2 - a i)) := by
    refine ⟨convex_univ, ?_⟩
    intro z _ w _ u v hu hv huv
    apply Finset.sup'_le
    intro i _
    have hz := Finset.le_sup' (fun i => inner ℝ (x i - (2 * c) • s i) z + c * ‖s i‖ ^ 2 - a i)
      (Finset.mem_univ i)
    have hw := Finset.le_sup' (fun i => inner ℝ (x i - (2 * c) • s i) w + c * ‖s i‖ ^ 2 - a i)
      (Finset.mem_univ i)
    have hzu := mul_le_mul_of_nonneg_left hz hu
    have hwv := mul_le_mul_of_nonneg_left hw hv
    simp only [inner_add_right, inner_smul_right, smul_eq_mul]
    have he : v = 1 - u := by linarith
    rw [he] at hwv ⊢
    nlinarith
  simpa only [quadraticEnvelope, add_sub_cancel_left] using hc

theorem quadraticEnvelope_lower (c : ℝ) (x s : ι → E) (a : ι → ℝ) (i : ι) (z : E) :
    inner ℝ (x i) z - a i + c * ‖z - s i‖ ^ 2 ≤ quadraticEnvelope c x s a z := by
  have hh := Finset.le_sup' (fun i => inner ℝ (x i - (2 * c) • s i) z + c * ‖s i‖ ^ 2 - a i)
    (Finset.mem_univ i)
  change _ ≤ c * ‖z‖ ^ 2 + _
  calc
    inner ℝ (x i) z - a i + c * ‖z - s i‖ ^ 2 =
        c * ‖z‖ ^ 2 + (inner ℝ (x i - (2 * c) • s i) z + c * ‖s i‖ ^ 2 - a i) := by
      rw [norm_sub_sq_real]
      simp only [inner_sub_left, real_inner_smul_left]
      rw [real_inner_comm (s i) z]
      ring
    _ ≤ _ := by simpa only [add_comm] using add_le_add_left hh (c * ‖z‖ ^ 2)

theorem quadraticEnvelope_upper (c : ℝ) (x s : ι → E) (a : ι → ℝ) (z : E) (r : ℝ)
    (hr : ∀ i, inner ℝ (x i) z - a i + c * ‖z - s i‖ ^ 2 ≤ r) :
    quadraticEnvelope c x s a z ≤ r := by
  have hs : Finset.univ.sup' Finset.univ_nonempty
      (fun i => inner ℝ (x i - (2 * c) • s i) z + c * ‖s i‖ ^ 2 - a i) ≤ r - c * ‖z‖ ^ 2 := by
    apply Finset.sup'_le
    intro i _
    have hh := hr i
    rw [norm_sub_sq_real] at hh
    simp only [inner_sub_left, real_inner_smul_left]
    rw [real_inner_comm (s i) z] at hh
    linarith
  unfold quadraticEnvelope
  linarith

theorem quadraticEnvelope_sample (c : ℝ) (x s : ι → E) (a : ι → ℝ)
    (hi : ∀ i j, c * ‖s i - s j‖ ^ 2 ≤ a i - a j - inner ℝ (s j) (x i - x j)) (i : ι) :
    quadraticEnvelope c x s a (s i) = inner ℝ (x i) (s i) - a i := by
  apply le_antisymm
  · apply quadraticEnvelope_upper
    intro j
    have hh := hi j i
    rw [norm_sub_rev (s j) (s i)] at hh
    simp only [inner_sub_right] at hh
    rw [real_inner_comm (x j) (s i), real_inner_comm (x i) (s i)] at hh
    linarith
  · simpa using quadraticEnvelope_lower c x s a i (s i)

theorem quadraticEnvelope_sample_gap (c : ℝ) (x s : ι → E) (a : ι → ℝ)
    (hi : ∀ i j, c * ‖s i - s j‖ ^ 2 ≤ a i - a j - inner ℝ (s j) (x i - x j))
    (i : ι) (z : E) :
    quadraticEnvelope c x s a (s i) + inner ℝ (x i) (z - s i) + c * ‖z - s i‖ ^ 2 ≤
      quadraticEnvelope c x s a z := by
  rw [quadraticEnvelope_sample c x s a hi, inner_sub_right]
  linarith [quadraticEnvelope_lower c x s a i z]

end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof
open ShorNonsmooth.AlmostDiff

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem strong_linear_min_exists {h : E → ℝ} {c : ℝ} (hc : 0 < c)
    (hcont : Continuous h)
    (hconv : ConvexOn ℝ Set.univ (fun z => h z - c * ‖z‖ ^ 2)) (x : E) :
    ∃ p, ∀ z, h p - inner ℝ x p ≤ h z - inner ℝ x z := by
  obtain ⟨u, hu⟩ := exists_subgradient hconv 0
  apply (hcont.sub (by fun_prop : Continuous (fun z => inner ℝ x z))).exists_forall_le' 0
  filter_upwards [((tendsto_norm_cocompact_atTop : Tendsto (fun z : E => ‖z‖)
    (cocompact E) atTop).eventually_ge_atTop (‖u - x‖ / c))] with z hz
  have hcz : ‖u - x‖ ≤ c * ‖z‖ := by
    have ht := (div_le_iff₀ hc).mp hz
    nlinarith
  have hs := mul_le_mul_of_nonneg_right hcz (norm_nonneg z)
  have hh := hu z
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero] at hh
  have hi := (abs_le.mp (abs_real_inner_le_norm (u - x) z)).1
  rw [inner_sub_left] at hi
  change h 0 - inner ℝ x (0 : E) ≤ h z - inner ℝ x z
  rw [inner_zero_right, sub_zero]
  nlinarith

theorem attained_smooth_conjugate {h : E → ℝ} {M : ℝ} (hM : 0 < M)
    (hcont : Continuous h)
    (hconv : ConvexOn ℝ Set.univ (fun z => h z - (1 / (2 * M)) * ‖z‖ ^ 2)) :
    ∃ (F : E → ℝ) (p : E → E),
      ConvexOn ℝ Set.univ F ∧
      (∀ x, HasGradientAt F (p x) x) ∧
      (∀ x y, ‖p x - p y‖ ≤ M * ‖x - y‖) ∧
      (∀ x, F x = inner ℝ x (p x) - h (p x)) ∧
      (∀ x z, h (p x) - inner ℝ x (p x) + (1 / (2 * M)) * ‖z - p x‖ ^ 2 ≤
        h z - inner ℝ x z) := by
  have hc : 0 < 1 / (2 * M) := by positivity
  choose p hp using strong_linear_min_exists hc hcont hconv
  have hgap (x z : E) : h (p x) - inner ℝ x (p x) + (1 / (2 * M)) * ‖z - p x‖ ^ 2 ≤
      h z - inner ℝ x z := strong_linear_min_gap hconv (hp x) z
  have hLip (x y : E) : ‖p x - p y‖ ≤ M * ‖x - y‖ := by
    have hx := hgap x (p y)
    have hy := hgap y (p x)
    rw [norm_sub_rev (p y) (p x)] at hx
    have hs : 2 * (1 / (2 * M)) * ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
      simp only [inner_sub_left, inner_sub_right]
      linarith
    have hcs := real_inner_le_norm (x - y) (p x - p y)
    have hm := mul_le_mul_of_nonneg_left (hs.trans hcs) hM.le
    have he : M * (2 * (1 / (2 * M))) = 1 := by field_simp
    rw [← mul_assoc, he, one_mul] at hm
    by_cases hz : ‖p x - p y‖ = 0
    · rw [hz]
      positivity
    · have hp0 : 0 < ‖p x - p y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  let F : E → ℝ := fun x => inner ℝ x (p x) - h (p x)
  have hdual (x z : E) : inner ℝ x z - h z ≤ F x := by
    dsimp [F]
    linarith [hp x z]
  have hF : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hx := mul_le_mul_of_nonneg_left (hdual x (p (a • x + b • y))) ha
    have hy := mul_le_mul_of_nonneg_left (hdual y (p (a • x + b • y))) hb
    change F (a • x + b • y) ≤ a * F x + b * F y
    dsimp only [F] at hx hy ⊢
    simp only [inner_add_left, real_inner_smul_left]
    have hh : (a + b) * h (p (a • x + b • y)) = h (p (a • x + b • y)) := by rw [hab, one_mul]
    linarith
  have hgrad (x : E) : HasGradientAt F (p x) x := by
    apply quadratic_remainder_gradient (C := M)
    intro v
    have hlo := hdual (x + v) (p x)
    have hhi := hdual x (p (x + v))
    have hi := real_inner_le_norm (p (x + v) - p x) v
    have hl := hLip (x + v) x
    simp only [add_sub_cancel_left] at hl
    have hb := mul_le_mul_of_nonneg_right hl (norm_nonneg v)
    simp only [inner_sub_left] at hi
    dsimp [F] at hlo hhi ⊢
    simp only [inner_add_left] at hlo ⊢
    rw [real_inner_comm (p x) v] at hlo
    rw [real_inner_comm (p (x + v)) v] at hlo ⊢
    constructor <;> nlinarith
  exact ⟨F, p, hF, hgrad, hLip, fun _ => rfl, hgap⟩

end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof
open TaylorHG.PEP

variable {d : ℕ} {ι : Type*}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem interp_iff_shifted (μ L : NNReal) (hμL : μ < L)
    (x g : ι → E) (fv : ι → ℝ) (i j : ι) :
    InterpIneq μ (L : ENNReal) x g fv i j ↔
    (1 / (2 * ((L : ℝ) - (μ : ℝ)))) *
      ‖(g i - (μ : ℝ) • x i) - (g j - (μ : ℝ) • x j)‖ ^ 2 ≤
      (fv i - (μ : ℝ) / 2 * ‖x i‖ ^ 2) - (fv j - (μ : ℝ) / 2 * ‖x j‖ ^ 2) -
        inner ℝ (g j - (μ : ℝ) • x j) (x i - x j) := by
  have hμ : (0 : ℝ) ≤ μ := μ.coe_nonneg
  have hL : (0 : ℝ) < L := lt_of_le_of_lt hμ (show (μ : ℝ) < (L : ℝ) from hμL)
  have hM : (0 : ℝ) < (L : ℝ) - (μ : ℝ) := sub_pos.mpr (show (μ : ℝ) < (L : ℝ) from hμL)
  have hd : 1 - (μ : ℝ) * (L : ℝ)⁻¹ = ((L : ℝ) - (μ : ℝ)) / (L : ℝ) := by
    field_simp
  have he : (g i - (μ : ℝ) • x i) - (g j - (μ : ℝ) • x j) =
      (g i - g j) - (μ : ℝ) • (x i - x j) := by module
  have hid : fv i - fv j - inner ℝ (g j) (x i - x j) -
      (1 / (2 * (1 - (μ : ℝ) * (L : ℝ)⁻¹))) *
        ((L : ℝ)⁻¹ * ‖g i - g j‖ ^ 2 + (μ : ℝ) * ‖x i - x j‖ ^ 2 -
          2 * ((μ : ℝ) * (L : ℝ)⁻¹) * inner ℝ (g j - g i) (x j - x i)) =
      (fv i - (μ : ℝ) / 2 * ‖x i‖ ^ 2) - (fv j - (μ : ℝ) / 2 * ‖x j‖ ^ 2) -
        inner ℝ (g j - (μ : ℝ) • x j) (x i - x j) -
          (1 / (2 * ((L : ℝ) - (μ : ℝ)))) *
            ‖(g i - (μ : ℝ) • x i) - (g j - (μ : ℝ) • x j)‖ ^ 2 := by
    rw [hd, he]
    simp only [norm_sub_sq_real, norm_smul, Real.norm_of_nonneg hμ,
      inner_sub_left, inner_sub_right, inner_smul_right,
      real_inner_comm]
    simp only [mul_pow, norm_sub_sq_real, real_inner_self_eq_norm_sq]
    field_simp
    ring
  unfold InterpIneq
  simp only [ENNReal.toReal_inv, ENNReal.coe_toReal]
  constructor <;> intro hh <;> linarith

end PEPExactProof

noncomputable section
open Set Filter
open scoped Topology NNReal ENNReal Classical
namespace PEPExactProof
open TaylorHG.PEP ShorNonsmooth.AlmostDiff

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem smooth_finite_interpolation {M : ℝ} (hM : 0 < M)
    (x s : ι → E) (a : ι → ℝ)
    (hi : ∀ i j, (1 / (2 * M)) * ‖s i - s j‖ ^ 2 ≤
      a i - a j - inner ℝ (s j) (x i - x j)) :
    ∃ (F : E → ℝ) (p : E → E), ConvexOn ℝ Set.univ F ∧
      (∀ y, HasGradientAt F (p y) y) ∧
      (∀ y z, ‖p y - p z‖ ≤ M * ‖y - z‖) ∧
      (∀ i, F (x i) = a i ∧ p (x i) = s i) := by
  let h := quadraticEnvelope (1 / (2 * M)) x s a
  obtain ⟨F, p, hcv, hgrad, hLip, hF, hgap⟩ := attained_smooth_conjugate hM
    (quadraticEnvelope_continuous (1 / (2 * M)) x s a)
    (quadraticEnvelope_shift_convex (1 / (2 * M)) x s a)
  refine ⟨F, p, hcv, hgrad, hLip, ?_⟩
  intro i
  have hp : p (x i) = s i := by
    have hs := quadraticEnvelope_sample_gap (1 / (2 * M)) x s a hi i (p (x i))
    have hg := hgap (x i) (s i)
    have hc : 0 < 1 / (2 * M) := by positivity
    rw [inner_sub_right] at hs
    have hn : ‖s i - p (x i)‖ ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg ‖p (x i) - s i‖]
    have hz : ‖s i - p (x i)‖ = 0 := by nlinarith [norm_nonneg (s i - p (x i))]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  refine ⟨?_, hp⟩
  rw [hF, hp, quadraticEnvelope_sample (1 / (2 * M)) x s a hi]
  ring

theorem interpolation_of_shifted (μ L : NNReal) (hμL : μ < L)
    (x g : ι → E) (fv : ι → ℝ)
    (hi : ∀ i j, (1 / (2 * ((L : ℝ) - (μ : ℝ)))) *
      ‖(g i - (μ : ℝ) • x i) - (g j - (μ : ℝ) • x j)‖ ^ 2 ≤
      (fv i - (μ : ℝ) / 2 * ‖x i‖ ^ 2) - (fv j - (μ : ℝ) / 2 * ‖x j‖ ^ 2) -
        inner ℝ (g j - (μ : ℝ) • x j) (x i - x j)) :
    ∃ f : E → ℝ, FClass μ (L : ENNReal) f ∧
      ∀ i, f (x i) = fv i ∧ HasGradientAt f (g i) (x i) := by
  have hμ : (0 : ℝ) ≤ μ := μ.coe_nonneg
  have hM : 0 < (L : ℝ) - (μ : ℝ) := sub_pos.mpr (show (μ : ℝ) < (L : ℝ) from hμL)
  have hL : (0 : ℝ) < L := lt_of_le_of_lt hμ (show (μ : ℝ) < (L : ℝ) from hμL)
  obtain ⟨F, p, hcv, hgrad, hLip, hsample⟩ := smooth_finite_interpolation hM x
    (fun i => g i - (μ : ℝ) • x i) (fun i => fv i - (μ : ℝ) / 2 * ‖x i‖ ^ 2) hi
  let f : E → ℝ := fun y => F y + (μ : ℝ) / 2 * ‖y‖ ^ 2
  have hq : ConvexOn ℝ Set.univ (fun y : E => (μ : ℝ) / 2 * ‖y‖ ^ 2) := by
    simpa only [smul_eq_mul, Pi.pow_apply] using
      ((convexOn_univ_norm : ConvexOn ℝ Set.univ (fun y : E => ‖y‖)).pow
        (fun y _ => norm_nonneg y) 2).smul
        (show 0 ≤ (μ : ℝ) / 2 by positivity)
  have hf : ConvexOn ℝ Set.univ f := hcv.add hq
  have hfg (y : E) : HasGradientAt f (p y + (μ : ℝ) • y) y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    dsimp only [f]
    rw [map_add]
    exact (hgrad y).hasFDerivAt.add (quadratic_hasGradient (μ : ℝ) y).hasFDerivAt
  have hfl (y z : E) : ‖(p y + (μ : ℝ) • y) - (p z + (μ : ℝ) • z)‖ ≤ (L : ℝ) * ‖y - z‖ := by
    have he : (p y + (μ : ℝ) • y) - (p z + (μ : ℝ) • z) =
        (p y - p z) + (μ : ℝ) • (y - z) := by module
    rw [he]
    calc
      ‖(p y - p z) + (μ : ℝ) • (y - z)‖ ≤ ‖p y - p z‖ + ‖(μ : ℝ) • (y - z)‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖y - z‖ := by
        rw [norm_smul, Real.norm_of_nonneg hμ]
        nlinarith [hLip y z]
  refine ⟨f, ⟨hf, ?_, ?_⟩, ?_⟩
  · intro y z u v hu hv
    rw [subgradient_eq_gradient hu (hfg y), subgradient_eq_gradient hv (hfg z)]
    simp only [ENNReal.toReal_inv, ENNReal.coe_toReal]
    calc
      (L : ℝ)⁻¹ * ‖(p y + (μ : ℝ) • y) - (p z + (μ : ℝ) • z)‖ ≤
          (L : ℝ)⁻¹ * ((L : ℝ) * ‖y - z‖) := mul_le_mul_of_nonneg_left (hfl y z) (inv_nonneg.mpr hL.le)
      _ = ‖y - z‖ := by field_simp
  · simpa only [f, add_sub_cancel_right] using hcv
  · intro i
    refine ⟨?_, ?_⟩
    · dsimp [f]
      rw [(hsample i).1]
      ring
    · have he : p (x i) + (μ : ℝ) • x i = g i := by rw [(hsample i).2]; module
      simpa only [he] using hfg (x i)

theorem finite_interpolation (μ L : NNReal) (hμL : μ < L)
    (x g : ι → E) (fv : ι → ℝ)
    (hi : ∀ i j, InterpIneq μ (L : ENNReal) x g fv i j) :
    ∃ f : E → ℝ, FClass μ (L : ENNReal) f ∧
      ∀ i, f (x i) = fv i ∧ HasGradientAt f (g i) (x i) := by
  apply interpolation_of_shifted μ L hμL x g fv
  intro i j
  exact (interp_iff_shifted μ L hμL x g fv i j).mp (hi i j)

end PEPExactProof

noncomputable section
open Set Matrix
open scoped Topology NNReal ENNReal Classical MatrixOrder
namespace PEPExactProof
open TaylorHG.PEP
variable {d N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

noncomputable def represent (col : Fin (N + 2) → E) (v : Fin (N + 2) → ℝ) : E :=
  ∑ a, v a • col a

theorem represent_add (col : Fin (N + 2) → E) (v w : Fin (N + 2) → ℝ) :
    represent col (v + w) = represent col v + represent col w := by
  simp [represent, add_smul, Finset.sum_add_distrib]

theorem represent_sub (col : Fin (N + 2) → E) (v w : Fin (N + 2) → ℝ) :
    represent col (v - w) = represent col v - represent col w := by
  simp [represent, sub_smul, Finset.sum_sub_distrib]

theorem represent_smul (col : Fin (N + 2) → E) (c : ℝ) (v : Fin (N + 2) → ℝ) :
    represent col (c • v) = c • represent col v := by
  simp [represent, mul_smul, Finset.smul_sum]

theorem represent_single (col : Fin (N + 2) → E) (a : Fin (N + 2)) :
    represent col (Pi.single a 1) = col a := by
  simp [represent, Pi.single_apply]

theorem represent_sum {ι : Type*} [Fintype ι] (col : Fin (N + 2) → E)
    (v : ι → Fin (N + 2) → ℝ) :
    represent col (∑ i, v i) = ∑ i, represent col (v i) := by
  simp only [represent, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem trace_outer (col : Fin (N + 2) → E) (v w : Fin (N + 2) → ℝ) :
    (gramOf col * outer v w).trace = inner ℝ (represent col v) (represent col w) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramOf, outer, represent,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm (col i) (col j)]
  ring

theorem gram_posSemidef (col : Fin (N + 2) → E) : (gramOf col).PosSemidef := by
  let A : Matrix (Fin d) (Fin (N + 2)) ℝ := fun i j => col j i
  have he : gramOf col = Aᴴ * A := by
    ext i j
    change inner ℝ (col i) (col j) = ∑ k, star (A k i) * A k j
    simp [PiLp.inner_apply, A, RCLike.inner_apply, mul_comm]
  rw [he]
  exact Matrix.posSemidef_conjTranspose_mul_self A

theorem gram_realization (hd : N + 2 ≤ d)
    (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hG : G.PosSemidef) :
    ∃ col : Fin (N + 2) → E, gramOf col = G := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg
  let col : Fin (N + 2) → E := fun j =>
    ∑ a : Fin (N + 2), EuclideanSpace.single (Fin.castLE hd a) (B a j)
  refine ⟨col, ?_⟩
  rw [hB]
  ext i j
  simp only [gramOf, col, sum_inner, inner_sum, EuclideanSpace.inner_single_left,
    PiLp.single_apply, star_trivial, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply]
  simp only [Fin.castLE_inj, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply, star_trivial]

@[simp] theorem point_star (H : Matrix (Fin N) (Fin N) ℝ) (col : Fin (N + 2) → E) :
    pointOf H col none = 0 := by simp [pointOf, hvec]

@[simp] theorem grad_star (col : Fin (N + 2) → E) : gradOf col none = 0 := by
  simp [gradOf, uvec]

@[simp] theorem grad_some (col : Fin (N + 2) → E) (i : Fin (N + 1)) :
    gradOf col (some i) = col (Fin.castSucc i) := by
  exact represent_single col (Fin.castSucc i)

theorem point_some (H : Matrix (Fin N) (Fin N) ℝ) (col : Fin (N + 2) → E)
    (i : Fin (N + 1)) : pointOf H col (some i) =
      col (Fin.last (N + 1)) - ∑ k, hcoef H i k • col (Fin.castSucc k) := by
  change represent col (Pi.single _ 1 - ∑ k, hcoef H i k • Pi.single _ 1) = _
  rw [represent_sub, represent_single, represent_sum]
  simp only [represent_smul, represent_single]

@[simp] theorem point_zero (H : Matrix (Fin N) (Fin N) ℝ) (col : Fin (N + 2) → E) :
    pointOf H col (some 0) = col (Fin.last (N + 1)) := by
  rw [point_some]
  simp [hcoef]

theorem radius_trace (col : Fin (N + 2) → E) :
    (gramOf col * ARmat N).trace = ‖col (Fin.last (N + 1))‖ ^ 2 := by
  rw [ARmat, trace_outer, represent_single]
  exact real_inner_self_eq_norm_sq _

end PEPExactProof

noncomputable section
open Set Matrix
open scoped Topology NNReal ENNReal Classical MatrixOrder
namespace PEPExactProof
open TaylorHG.PEP
variable {d N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem trace_Amat (μ L : NNReal) (H : Matrix (Fin N) (Fin N) ℝ)
    (col : Fin (N + 2) → E) (i j : Option (Fin (N + 1))) :
    (gramOf col * Amat μ L H i j).trace =
    (L : ℝ) / ((L : ℝ) - (μ : ℝ)) *
      inner ℝ (gradOf col j) (pointOf H col i - pointOf H col j) +
    1 / (2 * ((L : ℝ) - (μ : ℝ))) * ‖gradOf col i - gradOf col j‖ ^ 2 +
    (μ : ℝ) / ((L : ℝ) - (μ : ℝ)) *
      inner ℝ (gradOf col i) (pointOf H col j - pointOf H col i) +
    ((L : ℝ) * (μ : ℝ)) / (2 * ((L : ℝ) - (μ : ℝ))) *
      ‖pointOf H col i - pointOf H col j‖ ^ 2 := by
  simp only [Amat, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    trace_outer, represent_sub, real_inner_self_eq_norm_sq, smul_eq_mul]
  simp only [represent, pointOf, gradOf]
  simp only [real_inner_comm, div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem trace_Amat_shifted (μ L : NNReal) (hμL : μ < L)
    (H : Matrix (Fin N) (Fin N) ℝ) (col : Fin (N + 2) → E)
    (i j : Option (Fin (N + 1))) :
    (gramOf col * Amat μ L H i j).trace =
    inner ℝ (gradOf col j - (μ : ℝ) • pointOf H col j)
      (pointOf H col i - pointOf H col j) +
    (μ : ℝ) / 2 * (‖pointOf H col i‖ ^ 2 - ‖pointOf H col j‖ ^ 2) +
    ‖(gradOf col i - (μ : ℝ) • pointOf H col i) -
      (gradOf col j - (μ : ℝ) • pointOf H col j)‖ ^ 2 /
      (2 * ((L : ℝ) - (μ : ℝ))) := by
  rw [trace_Amat]
  let xi := pointOf H col i
  let xj := pointOf H col j
  let gi := gradOf col i
  let gj := gradOf col j
  change _ = inner ℝ (gj - (μ : ℝ) • xj) (xi - xj) +
    (μ : ℝ) / 2 * (‖xi‖ ^ 2 - ‖xj‖ ^ 2) +
    ‖(gi - (μ : ℝ) • xi) - (gj - (μ : ℝ) • xj)‖ ^ 2 / _
  have he : (gi - (μ : ℝ) • xi) - (gj - (μ : ℝ) • xj) =
      (gi - gj) - (μ : ℝ) • (xi - xj) := by module
  rw [he, norm_sub_sq_real (gi - gj) ((μ : ℝ) • (xi - xj)), norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, inner_smul_right, inner_sub_left, real_inner_smul_left]
  have hn := norm_sub_sq_real xi xj
  have hi : inner ℝ (gi - gj) (xi - xj) =
      inner ℝ gi (xi - xj) - inner ℝ gj (xi - xj) := inner_sub_left _ _ _
  have hx : inner ℝ xj (xi - xj) = inner ℝ xi xj - ‖xj‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm xi xj]
  have hr : inner ℝ gi (xj - xi) = -inner ℝ gi (xi - xj) := by
    rw [← neg_sub xi xj, inner_neg_right]
  dsimp [xi, xj, gi, gj] at *
  rw [hi, hx, hr]
  have hm : (L : ℝ) - (μ : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hμL)
  rw [hn]
  field_simp
  ring

end PEPExactProof

noncomputable section
open Set Matrix
open scoped Topology NNReal ENNReal Classical MatrixOrder
namespace PEPExactProof
open TaylorHG.PEP ShorNonsmooth.AlmostDiff
variable {d N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem forward_realization (μ L : NNReal) (hμL : μ < L) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N+1) → ℝ)
    (C : Matrix (Fin (N+2)) (Fin (N+2)) ℝ)
    (f : E → ℝ) (x : Fin (N+1) → E) (xs : E)
    (hf : FClass μ (L:ENNReal) f) (hmin : ∀ y, f xs ≤ f y)
    (hr : ‖x 0-xs‖ ≤ R) (hrun : IsFixedStepRun H f x) :
    ∃ G fv, SdpFeasible μ L R H G fv ∧
      criterion b C f xs x = b ⬝ᵥ fv + (C*G).trace := by
  have hL : 0 < L := lt_of_le_of_lt (zero_le : (0:NNReal) ≤ μ) hμL
  have hz : gradient f xs = 0 := by
    apply (subgradient_eq_gradient (g := (0:E)) (g' := gradient f xs) ?_
      (fclass_hasGradient hL hf xs).1).symm
    intro y
    simpa using sub_nonneg.mpr (hmin y)
  let col : Fin (N+2) → E := Fin.snoc (fun i => gradient f (x i)) (x 0-xs)
  let fv := fun i => f (x i)-f xs
  let xa : Option (Fin (N+1)) → E := fun i => i.elim xs x
  have hp (i : Option (Fin (N+1))) : pointOf H col i = xa i-xs := by
    cases i with
    | none => simp [xa, point_star]
    | some i =>
      rw [point_some]
      simp only [col, Fin.snoc_last, Fin.snoc_castSucc, xa, Option.elim_some]
      rw [hrun i]
      abel
  have hg (i : Option (Fin (N+1))) : gradOf col i = gradient f (xa i) := by
    cases i with
    | none => simpa [xa] using hz.symm
    | some i => simp [grad_some, col, xa]
  have hv (i : Option (Fin (N+1))) : fext fv i = f (xa i)-f xs := by
    cases i <;> simp [fext, fv, xa]
  refine ⟨gramOf col, fv, ⟨gram_posSemidef col, ?_, ?_⟩, rfl⟩
  · intro i j
    have hi := fclass_shifted_pairwise hμL hf (xa i) (xa j)
    have hn : InterpIneq μ (L:ENNReal) xa (fun i => gradient f (xa i)) (fun i => f (xa i)) i j := by
      apply (interp_iff_shifted μ L hμL _ _ _ i j).mpr
      simpa [div_eq_mul_inv, mul_comm] using hi
    have ht : InterpIneq μ (L:ENNReal) (pointOf H col) (gradOf col) (fext fv) i j := by
      unfold InterpIneq at hn ⊢
      simp only [hp, hg, hv]
      have he : (xa i-xs)-(xa j-xs) = xa i-xa j := by abel
      have he' : (xa j-xs)-(xa i-xs) = xa j-xa i := by abel
      rw [he, he']
      linarith
    have hs := (interp_iff_shifted μ L hμL _ _ _ i j).mp ht
    rw [trace_Amat_shifted μ L hμL]
    simp only [div_eq_mul_inv, one_mul] at hs ⊢
    nlinarith
  · rw [radius_trace]
    simp only [col, Fin.snoc_last]
    exact sq_le_sq₀ (norm_nonneg _) (le_trans (norm_nonneg _) hr) |>.mpr hr

end PEPExactProof

noncomputable section
open Set Matrix
open scoped Topology NNReal ENNReal Classical MatrixOrder
namespace PEPExactProof
open TaylorHG.PEP

variable {d N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem backward_realization (μ L : NNReal) (hμL : μ < L) (R : ℝ) (hR : 0 ≤ R)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hd : N + 2 ≤ d)
    (G : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (fv : Fin (N + 1) → ℝ)
    (hfeas : SdpFeasible μ L R H G fv) :
    ∃ (f : E → ℝ) (x : Fin (N + 1) → E) (xstar : E),
      FClass μ (L : ENNReal) f ∧ (∀ y, f xstar ≤ f y) ∧
      ‖x 0 - xstar‖ ≤ R ∧ IsFixedStepRun H f x ∧
      criterion b C f xstar x = b ⬝ᵥ fv + (C * G).trace := by
  obtain ⟨col, hcol⟩ := gram_realization hd G hfeas.1
  have hi : ∀ i j, (1 / (2 * ((L : ℝ) - (μ : ℝ)))) *
      ‖(gradOf col i - (μ : ℝ) • pointOf H col i) -
        (gradOf col j - (μ : ℝ) • pointOf H col j)‖ ^ 2 ≤
      (fext fv i - (μ : ℝ) / 2 * ‖pointOf H col i‖ ^ 2) -
        (fext fv j - (μ : ℝ) / 2 * ‖pointOf H col j‖ ^ 2) -
          inner ℝ (gradOf col j - (μ : ℝ) • pointOf H col j)
            (pointOf H col i - pointOf H col j) := by
    intro i j
    have hh := hfeas.2.1 i j
    rw [← hcol, trace_Amat_shifted μ L hμL] at hh
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  obtain ⟨f, hf, hsample⟩ := interpolation_of_shifted μ L hμL
    (pointOf H col) (gradOf col) (fext fv) hi
  let x : Fin (N + 1) → E := fun i => pointOf H col (some i)
  have hf0 : f 0 = 0 := by simpa only [point_star, fext] using (hsample none).1
  have hg0 : HasGradientAt f 0 0 := by
    simpa only [point_star, grad_star] using (hsample none).2
  have hmin (y : E) : f 0 ≤ f y := by
    have hh := gradient_subgradient hf.1 hg0 y
    simp only [inner_zero_left] at hh
    linarith
  have hgrad (i : Fin (N + 1)) : gradient f (x i) = col (Fin.castSucc i) := by
    simpa only [x, grad_some] using (hsample (some i)).2.gradient
  have hval (i : Fin (N + 1)) : f (x i) = fv i := by
    exact (hsample (some i)).1
  have hx0 : x 0 = col (Fin.last (N + 1)) := point_zero H col
  have hrad : ‖x 0 - (0 : E)‖ ≤ R := by
    have hh := hfeas.2.2
    rw [← hcol, radius_trace] at hh
    rw [sub_zero, hx0]
    nlinarith [norm_nonneg (col (Fin.last (N + 1)))]
  have hrun : IsFixedStepRun H f x := by
    intro i
    change pointOf H col (some i) = x 0 - ∑ k, hcoef H i k • gradient f (x k)
    rw [point_some, hx0]
    simp only [hgrad]
  have hcols : Fin.snoc (fun i => gradient f (x i)) (x 0 - (0 : E)) = col := by
    funext a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa only [Fin.snoc_last, sub_zero] using hx0
    · simpa only [Fin.snoc_castSucc] using hgrad i
  refine ⟨f, x, 0, hf, hmin, hrad, hrun, ?_⟩
  rw [criterion, hcols, hcol]
  simp only [hf0, sub_zero, hval]

end PEPExactProof

namespace TaylorHG.PEP

theorem theorem_5 {N : ℕ} (μ L : NNReal) (hμL : μ < L)
    (R : ℝ) (hR : 0 ≤ R) (H : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hC : C.IsSymm)
    (d : ℕ) (hd : N + 2 ≤ d) :
    worstCase d μ L R H b C = sdpValue μ L R H b C := by
  have _ := hC
  unfold worstCase sdpValue
  congr 1
  ext r
  constructor
  · rintro ⟨f, x, xs, hf, hm, hr, hx, he⟩
    obtain ⟨G, fv, hG, hv⟩ := PEPExactProof.forward_realization μ L hμL R H b C f x xs hf hm hr hx
    exact ⟨G, fv, hG, by rw [he, hv]⟩
  · rintro ⟨G, fv, hG, he⟩
    obtain ⟨f, x, xs, hf, hm, hr, hx, hv⟩ :=
      PEPExactProof.backward_realization μ L hμL R hR H b C hd G fv hG
    exact ⟨f, x, xs, hf, hm, hr, hx, by rw [he, hv]⟩

end TaylorHG.PEP

open TaylorHG.PEP
theorem solution {N : ℕ} (μ L : NNReal) (hμL : μ < L)
    (R : ℝ) (hR : 0 ≤ R) (H : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) (hC : C.IsSymm)
    (d : ℕ) (hd : N + 2 ≤ d) :
    worstCase d μ L R H b C = sdpValue μ L R H b C :=
  TaylorHG.PEP.theorem_5 μ L hμL R hR H b C hC d hd
