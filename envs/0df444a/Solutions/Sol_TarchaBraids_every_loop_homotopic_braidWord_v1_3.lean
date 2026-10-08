-- Prove2me | solution 3 for TarchaBraids.every_loop_homotopic_braidWord_v1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-04T18:02:08.745997+00:00
-- url     : https://prove2.me/submissions/80b23dd6-1637-447e-a3ad-6bbddd8d71b3

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1

/- ConfigurationClearance -/
section
set_option autoImplicit false
set_option maxHeartbeats 400000

open Set unitInterval

namespace BraidNormalForm

def configurations (n : ℕ) : Set (Fin n → ℂ) := {p | Function.Injective p}

lemma configurations_eq (n : ℕ) : configurations n =
    ⋂ i : Fin n, ⋂ j : Fin n, {p : Fin n → ℂ | i = j ∨ p i ≠ p j} := by
  ext p
  simp only [configurations, mem_ofPred_eq, mem_iInter]
  constructor
  · intro hp i j
    by_cases h : i = j
    · exact Or.inl h
    · exact Or.inr (fun he => h (hp he))
  · intro hp i j he
    rcases hp i j with h | h
    · exact h
    · exact False.elim (h he)

theorem configurations_open (n : ℕ) : IsOpen (configurations n) := by
  rw [configurations_eq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : i = j
  · simp only [h, true_or, ofPred_true]
    exact isOpen_univ
  · simp only [h, false_or]
    exact isOpen_ne_fun (continuous_apply i) (continuous_apply j)

theorem uniform_configuration_clearance (n : ℕ) (f : I → Fin n → ℂ)
    (hf : Continuous f) (hinj : ∀ t, Function.Injective (f t)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t : I) (q : Fin n → ℂ),
      dist q (f t) < ε → Function.Injective q := by
  have hc : IsCompact (range f) := isCompact_range hf
  have hs : range f ⊆ configurations n := by
    rintro _ ⟨t, rfl⟩
    exact hinj t
  obtain ⟨ε, hε, hthick⟩ := hc.exists_thickening_subset_open (configurations_open n) hs
  refine ⟨ε, hε, ?_⟩
  intro t q hq
  apply hthick
  exact Metric.mem_thickening_iff.mpr ⟨f t, ⟨t, rfl⟩, hq⟩

end BraidNormalForm
end

/- FiniteHyperplaneAvoidance -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set

namespace BraidNormalForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero real linear functional cannot vanish on a nonempty open set. -/
theorem exists_mem_open_linear_ne_zero (L : E →L[ℝ] ℝ) (hL : L ≠ 0)
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, L x ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hsub : U ⊆ (L.toLinearMap.ker : Set E) := fun x hx => h x hx
  have hi : (interior (L.toLinearMap.ker : Set E)).Nonempty :=
    hne.mono (interior_maximal hsub hU)
  have htop := L.toLinearMap.ker.eq_top_of_nonempty_interior' hi
  apply hL
  ext x
  have hx : x ∈ L.toLinearMap.ker := by rw [htop]; trivial
  exact hx

/-- Finitely many proper linear hyperplanes can be avoided in any nonempty open set. -/
theorem exists_mem_open_avoiding_linear_finset {ι : Type*} (s : Finset ι)
    (L : ι → E →L[ℝ] ℝ) (hL : ∀ i ∈ s, L i ≠ 0)
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i ∈ s, L i x ≠ 0 := by
  classical
  induction s using Finset.induction_on generalizing U with
  | empty =>
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, hx, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨x, hxU, hxi⟩ := exists_mem_open_linear_ne_zero (L i)
      (hL i (Finset.mem_insert_self i s)) hU hne
    have hopen : IsOpen (U ∩ {x | L i x ≠ 0}) :=
      hU.inter (isOpen_ne_fun (L i).continuous continuous_const)
    obtain ⟨y, hy, hys⟩ := ih (fun j hj => hL j (Finset.mem_insert_of_mem hj))
      hopen ⟨x, hxU, hxi⟩
    refine ⟨y, hy.1, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hy.2
    · exact hys j hj

/-- The finite-family form used to choose a generic configuration waypoint. -/
theorem exists_mem_open_avoiding_linear {ι : Type*} [Fintype ι]
    (L : ι → E →L[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, ∀ i, L i x ≠ 0 := by
  classical
  obtain ⟨x, hx, h⟩ := exists_mem_open_avoiding_linear_finset Finset.univ L
    (fun i _ => hL i) hU hne
  exact ⟨x, hx, fun i => h i (Finset.mem_univ i)⟩

end BraidNormalForm
end

/- CrossingDeterminant -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set

noncomputable section

namespace BraidNormalForm

/-- Unordered strand pairs are represented once, in increasing label order. -/
def StrandPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

instance (n : ℕ) : Fintype (StrandPair n) := inferInstanceAs (Fintype {p : Fin n × Fin n // p.1 < p.2})
instance (n : ℕ) : DecidableEq (StrandPair n) := inferInstanceAs (DecidableEq {p : Fin n × Fin n // p.1 < p.2})

def realGap {n : ℕ} (p : StrandPair n) : (Fin n → ℂ) →L[ℝ] ℝ where
  toFun x := (x p.val.1).re - (x p.val.2).re
  map_add' := by intro x y; simp only [Pi.add_apply, Complex.add_re]; ring
  map_smul' := by intro c x; simp; ring
  cont := by fun_prop

lemma realGap_ne_zero {n : ℕ} (p : StrandPair n) : realGap p ≠ 0 := by
  intro h
  have he := congrArg (fun L : (Fin n → ℂ) →L[ℝ] ℝ =>
    L (Function.update 0 p.val.1 1)) h
  have hne := ne_of_lt p.property
  simp [realGap, hne.symm] at he

lemma realGap_at_ne_zero {n : ℕ} {a : Fin n → ℂ}
    (ha : Function.Injective (fun j => (a j).re)) (p : StrandPair n) :
    realGap p a ≠ 0 := by
  intro h
  exact (ne_of_lt p.property) (ha (sub_eq_zero.mp h))

/-- The zero set is the locus where two affine crossing times coincide. -/
def crossingDet {n : ℕ} (a : Fin n → ℂ) (p q : StrandPair n) :
    (Fin n → ℂ) →L[ℝ] ℝ :=
  (realGap p a) • realGap q - (realGap q a) • realGap p

lemma crossingDet_apply {n : ℕ} (a c : Fin n → ℂ) (p q : StrandPair n) :
    crossingDet a p q c = realGap p a * realGap q c - realGap q a * realGap p c := rfl

lemma crossingDet_ne_zero {n : ℕ} {a : Fin n → ℂ}
    (ha : Function.Injective (fun j => (a j).re))
    {p q : StrandPair n} (hpq : p ≠ q) : crossingDet a p q ≠ 0 := by
  intro hz
  have hq := realGap_at_ne_zero ha q
  have hi : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
    by_contra h
    push Not at h
    have he := congrArg (fun L : (Fin n → ℂ) →L[ℝ] ℝ =>
      L (Function.update 0 p.val.1 1)) hz
    have hp := ne_of_lt p.property
    simp [crossingDet, realGap, h.1.symm, h.2.symm, hp.symm] at he
    apply hq
    change (a q.val.1).re - (a q.val.2).re = 0
    linarith
  have hj : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
    by_contra h
    push Not at h
    have he := congrArg (fun L : (Fin n → ℂ) →L[ℝ] ℝ =>
      L (Function.update 0 p.val.2 1)) hz
    have hp := ne_of_lt p.property
    simp [crossingDet, realGap, h.1.symm, h.2.symm, hp] at he
    apply hq
    change (a q.val.1).re - (a q.val.2).re = 0
    linarith
  apply hpq
  apply Subtype.ext
  apply Prod.ext
  · rcases hi with h | h
    · exact h
    · rcases hj with hj | hj
      · have hp := p.property
        have hq' := q.property
        omega
      · have hp := p.property
        omega
  · rcases hj with h | h
    · rcases hi with hi | hi
      · have hp := p.property
        omega
      · have hp := p.property
        have hq' := q.property
        omega
    · exact h

lemma realGap_lineMap {n : ℕ} (a c : Fin n → ℂ) (p : StrandPair n) (t : ℝ) :
    realGap p (AffineMap.lineMap a c t) = (1 - t) * realGap p a + t * realGap p c := by
  simp [AffineMap.lineMap_apply, realGap]
  ring

/-- Nonzero crossing determinants exclude simultaneous pair crossings. -/
theorem lineMap_crossing_unique {n : ℕ} {a c : Fin n → ℂ}
    (ha : Function.Injective (fun j => (a j).re))
    (hdet : ∀ p q : StrandPair n, p ≠ q → crossingDet a p q c ≠ 0)
    (t : ℝ) {p q : StrandPair n}
    (hp : realGap p (AffineMap.lineMap a c t) = 0)
    (hq : realGap q (AffineMap.lineMap a c t) = 0) : p = q := by
  by_contra hpq
  rw [realGap_lineMap] at hp hq
  have ht : t ≠ 0 := by
    intro h
    rw [h] at hp
    exact realGap_at_ne_zero ha p (by simpa using hp)
  have hp' : t * realGap p c = (t - 1) * realGap p a := by nlinarith [hp]
  have hq' : t * realGap q c = (t - 1) * realGap q a := by nlinarith [hq]
  apply hdet p q hpq
  apply (mul_eq_zero.mp (show t * crossingDet a p q c = 0 from ?_)).resolve_left ht
  rw [crossingDet_apply]
  calc
    t * (realGap p a * realGap q c - realGap q a * realGap p c) =
        realGap p a * (t * realGap q c) - realGap q a * (t * realGap p c) := by ring
    _ = 0 := by rw [hp', hq']; ring

/-- Every crossing is transverse because its affine difference has nonzero slope. -/
theorem lineMap_crossing_slope_ne_zero {n : ℕ} {a c : Fin n → ℂ}
    (ha : Function.Injective (fun j => (a j).re)) (p : StrandPair n) (t : ℝ)
    (hp : realGap p (AffineMap.lineMap a c t) = 0) :
    realGap p c - realGap p a ≠ 0 := by
  intro hs
  rw [realGap_lineMap] at hp
  have he := sub_eq_zero.mp hs
  rw [he] at hp
  apply realGap_at_ne_zero ha p
  nlinarith [hp]

/-- The affine real gap factors exactly at its crossing time. This will
identify the two adjacent real-order chambers on either side. -/
lemma realGap_lineMap_factor_at_zero {n : ℕ} (a c : Fin n → ℂ)
    (p : StrandPair n) (t s : ℝ)
    (ht : realGap p (AffineMap.lineMap a c t) = 0) :
    realGap p (AffineMap.lineMap a c s) =
      (s - t) * (realGap p c - realGap p a) := by
  rw [realGap_lineMap] at ht ⊢
  nlinarith [ht]

/-- If all other pairs are in increasing real order, a unique coincident
pair must occupy adjacent positions in that order. -/
theorem crossing_pair_adjacent {n : ℕ} (z : Fin n → ℂ) (p : StrandPair n)
    (hp : realGap p z = 0)
    (ho : ∀ k l : Fin n, k < l → (k ≠ p.val.1 ∨ l ≠ p.val.2) →
      (z k).re < (z l).re) : p.val.2.val = p.val.1.val + 1 := by
  have hlt : p.val.1.val < p.val.2.val := p.property
  by_contra hne
  have hgap : p.val.1.val + 1 < p.val.2.val := by omega
  let k : Fin n := ⟨p.val.1.val + 1, hgap.trans p.val.2.isLt⟩
  have hleft : p.val.1 < k := by change p.val.1.val < p.val.1.val + 1; omega
  have hright : k < p.val.2 := hgap
  have h₁ := ho p.val.1 k hleft (Or.inr (ne_of_lt hright))
  have h₂ := ho k p.val.2 hright (Or.inl (ne_of_gt hleft))
  have he : (z p.val.1).re = (z p.val.2).re := sub_eq_zero.mp hp
  linarith

end BraidNormalForm

end
end

/- LocalCrossingIsolation -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set unitInterval Filter Topology

namespace BraidNormalForm

/-- At a unique projected crossing, the colliding pair has nonzero imaginary
separation because the configuration itself is collision-free. -/
lemma crossing_imag_ne_zero {n : ℕ} (z : configurations n) (p : StrandPair n)
    (hp : realGap p z.val = 0) :
    (z.val p.val.1).im - (z.val p.val.2).im ≠ 0 := by
  intro him
  apply ne_of_lt p.property
  apply z.property
  apply Complex.ext
  · exact sub_eq_zero.mp hp
  · exact sub_eq_zero.mp him

/-- A unique crossing has a neighborhood where its imaginary order and every
other pair's real order remain fixed. This follows from continuity and the
finite number of strand pairs, without a smoothness hypothesis. -/
theorem unique_crossing_isolated {n : ℕ} {a b : configurations n}
    (γ : Path a b) (t₀ : I) (p : StrandPair n)
    (hp : realGap p (γ t₀).val = 0)
    (hunique : ∀ q : StrandPair n, realGap q (γ t₀).val = 0 → q = p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : I, dist t t₀ < δ →
      (((γ t₀).val p.val.1).im - ((γ t₀).val p.val.2).im) *
        (((γ t).val p.val.1).im - ((γ t).val p.val.2).im) > 0 ∧
      ∀ q : StrandPair n, q ≠ p →
        realGap q (γ t₀).val * realGap q (γ t).val > 0 := by
  let J := Option {q : StrandPair n // q ≠ p}
  let f : J → I → ℝ := fun j t => match j with
    | none => ((γ t).val p.val.1).im - ((γ t).val p.val.2).im
    | some q => realGap q.val (γ t).val
  have hc (k : Fin n) : Continuous (fun t : I => (γ t).val k) :=
    (continuous_apply k).comp (continuous_subtype_val.comp γ.continuous)
  have hf (j : J) : Continuous (f j) := by
    cases j with
    | none =>
      exact (Complex.continuous_im.comp (hc p.val.1)).sub
        (Complex.continuous_im.comp (hc p.val.2))
    | some q => exact (realGap q.val).continuous.comp (continuous_subtype_val.comp γ.continuous)
  have hn (j : J) : f j t₀ ≠ 0 := by
    cases j with
    | none => exact crossing_imag_ne_zero (γ t₀) p hp
    | some q => exact fun h => q.property (hunique q.val h)
  have he : ∀ᶠ t in 𝓝 t₀, ∀ j : J, 0 < f j t₀ * f j t := by
    apply Filter.eventually_all.mpr
    intro j
    exact continuousAt_const.eventually_lt
      ((continuous_const.mul (hf j)).continuousAt) (mul_self_pos.mpr (hn j))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  exact ⟨hd ht none, fun q hq => hd ht (some ⟨q, hq⟩)⟩

end BraidNormalForm
end

/- AffineSubpath -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open unitInterval

namespace BraidNormalForm

lemma affine_subpath {n : ℕ} {a b : configurations n} (p : Path a b)
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (s t u : I) :
    (p.subpath s t u).val =
      AffineMap.lineMap (p s).val (p t).val (u : ℝ) := by
  change (p (Set.Icc.convexComb s t u)).val = _
  rw [hp, hp s, hp t, Set.Icc.coe_convexComb, ← AffineMap.lineMap_apply_ring]
  exact (AffineMap.lineMap a.val b.val).apply_lineMap (s : ℝ) (t : ℝ) (u : ℝ)

/-- An affine pair beginning in strict increasing real order and crossing in
the interval must finish in the opposite order if the endpoint is not itself
a crossing. This supplies the actual swap, rather than assuming it. -/
lemma affine_crossing_reverses_order {n : ℕ} (a b : Fin n → ℂ) (p : StrandPair n)
    (hstart : realGap p a < 0) (hend : realGap p b ≠ 0)
    (t : I) (hc : realGap p (AffineMap.lineMap a b (t : ℝ)) = 0) :
    0 < realGap p b := by
  rw [realGap_lineMap] at hc
  have ht1 : (t : ℝ) < 1 := by
    by_contra h
    have he : (t : ℝ) = 1 := le_antisymm t.property.2 (le_of_not_gt h)
    rw [he] at hc
    exact hend (by simpa using hc)
  have hneg : (1 - (t : ℝ)) * realGap p a < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hstart
  by_contra h
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos t.property.1 (le_of_not_gt h)
  linarith

end BraidNormalForm
end

/- AffineCrossingFinite -/
section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace TarchaBraids.NormalForm

theorem affine_pair_crossings_subsingleton {ι : Type*} (a b : ι → ℝ)
    (ha : Function.Injective a) (i j : ι) :
    ({t : ℝ | i ≠ j ∧
      (1 - t) * a i + t * b i = (1 - t) * a j + t * b j}).Subsingleton := by
  intro x hx y hy
  have hs : b i - b j - a i + a j ≠ 0 := by
    intro hz
    have hzx : x * (b i - b j - a i + a j) = 0 := by rw [hz, mul_zero]
    have he : a i = a j := by nlinarith only [hx.2, hzx]
    exact hx.1 (ha he)
  have he : (x - y) * (b i - b j - a i + a j) = 0 := by
    nlinarith only [hx.2, hy.2]
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hs)

theorem affine_crossings_finite {ι : Type*} [Finite ι] (a b : ι → ℝ)
    (ha : Function.Injective a) :
    {t : ℝ | ∃ i j : ι, i ≠ j ∧
      (1 - t) * a i + t * b i = (1 - t) * a j + t * b j}.Finite := by
  have h := Set.finite_iUnion (fun i : ι => Set.finite_iUnion (fun j : ι =>
    (affine_pair_crossings_subsingleton a b ha i j).finite))
  simpa only [Set.ofPred_exists] using h

theorem complex_affine_crossings_finite {ι : Type*} [Finite ι] (a b : ι → ℂ)
    (ha : Function.Injective (fun i => (a i).re)) :
    {t : ℝ | ∃ i j : ι, i ≠ j ∧
      (((1 - t) • a i) + t • b i).re = (((1 - t) • a j) + t • b j).re}.Finite := by
  simpa only [Complex.add_re, Complex.smul_re, smul_eq_mul] using
    affine_crossings_finite (fun i => (a i).re) (fun i => (b i).re) ha

theorem lineMap_crossings_finite {ι : Type*} [Finite ι] (a b : ι → ℂ)
    (ha : Function.Injective (fun i => (a i).re)) :
    {t : ℝ | ∃ i j : ι, i ≠ j ∧
      (AffineMap.lineMap a b t i).re = (AffineMap.lineMap a b t j).re}.Finite := by
  simpa only [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply] using
    complex_affine_crossings_finite a b ha

theorem lineMap_crossings_finite_on {ι : Type*} [Finite ι] (a b : ι → ℂ)
    (ha : Function.Injective (fun i => (a i).re)) (S : Set ℝ) :
    {t : S | ∃ i j : ι, i ≠ j ∧
      (AffineMap.lineMap a b t.val i).re = (AffineMap.lineMap a b t.val j).re}.Finite := by
  exact Set.Finite.preimage (f := (Subtype.val : S → ℝ))
    (fun _ _ _ _ h => Subtype.ext h) (lineMap_crossings_finite a b ha)

end TarchaBraids.NormalForm
end

/- TimeWarp -/
section
set_option autoImplicit false

open Set unitInterval

namespace BraidNormalForm

def timeWarp (e x : ℝ) : ℝ := x + e * x * (1 - x)

@[simp] lemma timeWarp_zero (e : ℝ) : timeWarp e 0 = 0 := by simp [timeWarp]
@[simp] lemma timeWarp_one (e : ℝ) : timeWarp e 1 = 1 := by simp [timeWarp]

lemma timeWarp_sub (e x y : ℝ) :
    timeWarp e y - timeWarp e x = (y - x) * (1 + e - e * (x + y)) := by
  unfold timeWarp
  ring

lemma timeWarp_mem_Icc {e x : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) 1) : timeWarp e x ∈ Icc (0 : ℝ) 1 := by
  have hterm := mul_nonneg (mul_nonneg he0 hx.1) (sub_nonneg.mpr hx.2)
  have hex : e * x ≤ 1 :=
    (mul_le_mul_of_nonneg_left hx.2 he0).trans (by simpa using he1)
  have hupper := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hex)
  constructor <;> unfold timeWarp <;> nlinarith [hx.1, hx.2]

lemma timeWarp_strictMonoOn {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) :
    StrictMonoOn (timeWarp e) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hbound := mul_le_mul_of_nonneg_left (add_le_add hx.2 hy.2) he0
  have hfactor : 0 < 1 + e - e * (x + y) := by nlinarith
  have hpos := mul_pos (sub_pos.mpr hxy) hfactor
  exact sub_pos.mp (by simpa only [timeWarp_sub] using hpos)

lemma timeWarp_gap_le {e x y : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    timeWarp e y - timeWarp e x ≤ 2 * (y - x) := by
  have hprod := mul_nonneg he0 (add_nonneg hx.1 hy.1)
  have hfactor : 1 + e - e * (x + y) ≤ 2 := by linarith
  rw [timeWarp_sub]
  nlinarith [mul_le_mul_of_nonneg_left hfactor (sub_nonneg.mpr hxy)]

end BraidNormalForm
end

/- TimeWarpAvoidance -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set unitInterval

namespace BraidNormalForm

def warpedTime (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (t : I) : I :=
  ⟨timeWarp e t, timeWarp_mem_Icc he0 he1 t.property⟩

@[simp] lemma warpedTime_zero (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    warpedTime e he0 he1 0 = 0 := by
  apply Subtype.ext
  exact timeWarp_zero e

@[simp] lemma warpedTime_one (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    warpedTime e he0 he1 1 = 1 := by
  apply Subtype.ext
  exact timeWarp_one e

lemma warpedTime_strictMono (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    StrictMono (warpedTime e he0 he1.le) := by
  intro s t hst
  exact timeWarp_strictMonoOn he0 he1 s.property t.property hst

/-- A small increasing polynomial time change fixes both endpoints and avoids
any finite set of bad times at a prescribed finite family of sample points. -/
theorem exists_warped_samples_avoiding {m : ℕ} (t : Fin (m + 1) → I)
    {T : Set I} (hT : T.Finite) (hT0 : (0 : I) ∉ T) (hT1 : (1 : I) ∉ T)
    {eta : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ (e : ℝ) (he : e ∈ Ioo 0 eta),
      ∀ k, warpedTime e he.1.le (he.2.le.trans heta1) (t k) ∉ T := by
  classical
  let : Fintype T := hT.fintype
  let bad : (Fin (m + 1) × T) → ℝ := fun p =>
    ((p.2.val : ℝ) - (t p.1 : ℝ)) /
      ((t p.1 : ℝ) * (1 - (t p.1 : ℝ)))
  obtain ⟨e, he, hav⟩ := ((Ioo_infinite heta0).sdiff (finite_range bad)).nonempty
  refine ⟨e, he, ?_⟩
  intro k hk
  by_cases h0 : t k = 0
  · apply hT0
    simpa only [h0, warpedTime_zero] using hk
  by_cases h1 : t k = 1
  · apply hT1
    simpa only [h1, warpedTime_one] using hk
  let s : T := ⟨warpedTime e he.1.le (he.2.le.trans heta1) (t k), hk⟩
  have ht0 : (t k : ℝ) ≠ 0 := fun h => h0 (Subtype.ext h)
  have ht1 : 1 - (t k : ℝ) ≠ 0 := by
    intro h
    apply h1
    apply Subtype.ext
    change (t k : ℝ) = 1
    linarith
  have hd := mul_ne_zero ht0 ht1
  have heq : e = bad (k, s) := by
    apply (eq_div_iff hd).mpr
    change e * ((t k : ℝ) * (1 - (t k : ℝ))) = timeWarp e (t k) - (t k : ℝ)
    unfold timeWarp
    ring
  exact hav ⟨(k, s), heq.symm⟩

end BraidNormalForm
end

/- FiniteAvoidingSubdivision -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval Metric

noncomputable section

namespace BraidNormalForm

def uniformTime (m : ℕ) (hm : 0 < m) (k : Fin (m + 1)) : I :=
  ⟨(k.val : ℝ) / m, by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) hmR.le
    · apply (div_le_one hmR).mpr
      exact_mod_cast (Nat.le_of_lt_succ k.isLt)⟩

@[simp] lemma uniformTime_zero (m : ℕ) (hm : 0 < m) : uniformTime m hm 0 = 0 := by
  apply Subtype.ext
  simp [uniformTime]

@[simp] lemma uniformTime_last (m : ℕ) (hm : 0 < m) :
    uniformTime m hm (Fin.last m) = 1 := by
  apply Subtype.ext
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [uniformTime, hmR]

lemma uniformTime_strictMono (m : ℕ) (hm : 0 < m) : StrictMono (uniformTime m hm) := by
  intro i j hij
  change (i.val : ℝ) / m < (j.val : ℝ) / m
  apply (div_lt_div_iff_of_pos_right (by exact_mod_cast hm : (0 : ℝ) < m)).mpr
  exact_mod_cast hij

lemma uniformTime_gap (m : ℕ) (hm : 0 < m) (k : Fin m) :
    (uniformTime m hm k.succ : ℝ) - (uniformTime m hm k.castSucc : ℝ) = 1 / m := by
  simp only [uniformTime, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

/-- An open cover has a finite strictly increasing subdivision whose vertices
avoid a prescribed finite subset of the interior. Each closed subinterval
lies in one member of the cover. -/
theorem finite_open_subdivision_avoiding {J : Type*} (C : J → Set I)
    (hC : ∀ j, IsOpen (C j)) (hcover : univ ⊆ ⋃ j, C j)
    {T : Set I} (hT : T.Finite) (hT0 : (0 : I) ∉ T) (hT1 : (1 : I) ∉ T) :
    ∃ (m : ℕ) (t : Fin (m + 1) → I) (c : Fin m → J),
      t 0 = 0 ∧ t (Fin.last m) = 1 ∧ StrictMono t ∧
      (∀ k, t k ∉ T) ∧
      ∀ k : Fin m, Icc (t k.castSucc) (t k.succ) ⊆ C (c k) := by
  classical
  obtain ⟨delta, hdelta, hball⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_univ : IsCompact (univ : Set I)) hC hcover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hdelta)
  let m := n + 1
  have hm : 0 < m := Nat.succ_pos n
  have hmesh : 2 / (m : ℝ) < delta := by
    dsimp only [m]
    push_cast
    calc
      2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
      _ < 2 * (delta / 2) := mul_lt_mul_of_pos_left hn (by norm_num)
      _ = delta := by ring
  obtain ⟨e, he, hav⟩ := exists_warped_samples_avoiding (uniformTime m hm)
    hT hT0 hT1 (by norm_num : (0 : ℝ) < 1) le_rfl
  let t : Fin (m + 1) → I := fun k =>
    warpedTime e he.1.le he.2.le (uniformTime m hm k)
  have hmono : StrictMono t := (warpedTime_strictMono e he.1.le he.2).comp
    (uniformTime_strictMono m hm)
  have hc : ∀ k : Fin m, ∃ j, ball (t k.castSucc) delta ⊆ C j :=
    fun k => hball (t k.castSucc) (mem_univ _)
  choose c hc using hc
  refine ⟨m, t, c, ?_, ?_, hmono, hav, ?_⟩
  · simp [t]
  · simp [t]
  · intro k s hs
    apply hc k
    have hgap : (t k.succ : ℝ) - (t k.castSucc : ℝ) ≤ 2 / (m : ℝ) := by
      have h := timeWarp_gap_le he.1.le he.2.le
        (uniformTime m hm k.castSucc).property (uniformTime m hm k.succ).property
        ((uniformTime_strictMono m hm).monotone (by
          change k.val ≤ k.val + 1
          omega))
      change timeWarp e (uniformTime m hm k.succ) -
        timeWarp e (uniformTime m hm k.castSucc) ≤ 2 / (m : ℝ)
      calc
        _ ≤ 2 * ((uniformTime m hm k.succ : ℝ) -
          (uniformTime m hm k.castSucc : ℝ)) := h
        _ = 2 / (m : ℝ) := by rw [uniformTime_gap]; ring
    change dist (s : ℝ) (t k.castSucc : ℝ) < delta
    have hsL : (t k.castSucc : ℝ) ≤ (s : ℝ) := hs.1
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hsL)]
    have hsR : (s : ℝ) ≤ (t k.succ : ℝ) := hs.2
    linarith

end BraidNormalForm

end
end

/- PairCrossingCharts -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval Metric

namespace BraidNormalForm

def selectedPair {n : ℕ} (p : StrandPair n) (k l : Fin n) : Prop :=
  (k = p.val.1 ∧ l = p.val.2) ∨ (k = p.val.2 ∧ l = p.val.1)

lemma exists_relabelled_pair {n : ℕ} (perm : Equiv.Perm (Fin n)) (p : StrandPair n) :
    ∃ q : StrandPair n, ∀ k l : Fin n,
      selectedPair q k l ↔ selectedPair p (perm k) (perm l) := by
  have hne : perm.symm p.val.1 ≠ perm.symm p.val.2 :=
    fun h => (ne_of_lt p.property) (perm.symm.injective h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨⟨(perm.symm p.val.1, perm.symm p.val.2), hlt⟩, ?_⟩
    intro k l
    simp only [selectedPair, ← perm.eq_symm_apply]
  · refine ⟨⟨(perm.symm p.val.2, perm.symm p.val.1), hgt⟩, ?_⟩
    intro k l
    simp only [selectedPair, ← perm.eq_symm_apply, or_comm]

def PairChart {n : ℕ} (f : I → configurations n) (p : StrandPair n) (U : Set I) : Prop :=
  (∀ t ∈ U, ((f t).val p.val.1).im ≠ ((f t).val p.val.2).im) ∧
  (∀ t ∈ U, ∀ k l : Fin n, k ≠ l → ¬ selectedPair p k l →
    ((f t).val k).re ≠ ((f t).val l).re)

def GoodChart {n : ℕ} (f : I → configurations n) (U : Set I) : Prop :=
  (∀ t ∈ U, Function.Injective (fun k => ((f t).val k).re)) ∨
    ∃ p : StrandPair n, PairChart f p U

lemma real_injective_iff_gaps {n : ℕ} (z : Fin n → ℂ) :
    Function.Injective (fun k => (z k).re) ↔ ∀ p : StrandPair n, realGap p z ≠ 0 := by
  constructor
  · exact fun h p => realGap_at_ne_zero h p
  · intro h k l he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h ⟨(k, l), hlt⟩ (sub_eq_zero.mpr he)
    · exact h ⟨(l, k), hgt⟩ (sub_eq_zero.mpr he.symm)

lemma other_gaps_imply_separation {n : ℕ} (z : Fin n → ℂ) (p : StrandPair n)
    (h : ∀ q : StrandPair n, q ≠ p → realGap q z ≠ 0)
    (k l : Fin n) (hkl : k ≠ l) (hex : ¬ selectedPair p k l) :
    (z k).re ≠ (z l).re := by
  intro he
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · let q : StrandPair n := ⟨(k, l), hlt⟩
    have hqp : q ≠ p := by
      intro hp
      have hh := congrArg Subtype.val hp
      exact hex (Or.inl ⟨congrArg Prod.fst hh, congrArg Prod.snd hh⟩)
    exact h q hqp (sub_eq_zero.mpr he)
  · let q : StrandPair n := ⟨(l, k), hgt⟩
    have hqp : q ≠ p := by
      intro hp
      have hh := congrArg Subtype.val hp
      exact hex (Or.inr ⟨congrArg Prod.snd hh, congrArg Prod.fst hh⟩)
    exact h q hqp (sub_eq_zero.mpr he.symm)

/-- Every point of a path with unique crossing pairs has an open chart that
is crossing-free or keeps just one possible pair, separated in height. -/
theorem exists_pair_chart {n : ℕ} {a b : configurations n} (γ : Path a b)
    (hunique : ∀ t (p q : StrandPair n), realGap p (γ t).val = 0 →
      realGap q (γ t).val = 0 → p = q) (t₀ : I) :
    ∃ U : Set I, IsOpen U ∧ t₀ ∈ U ∧ GoodChart γ U := by
  classical
  by_cases hgood : Function.Injective (fun k => ((γ t₀).val k).re)
  · let U : Set I := {t | Function.Injective (fun k => ((γ t).val k).re)}
    have hU : U = ⋂ p : StrandPair n, {t | realGap p (γ t).val ≠ 0} := by
      ext t
      simp only [U, mem_ofPred_eq, mem_iInter, real_injective_iff_gaps]
    refine ⟨U, ?_, hgood, Or.inl (fun _ ht => ht)⟩
    rw [hU]
    apply isOpen_iInter_of_finite
    intro p
    exact isOpen_ne_fun ((realGap p).continuous.comp
      (continuous_subtype_val.comp γ.continuous)) continuous_const
  · have hbad : ¬ ∀ p : StrandPair n, realGap p (γ t₀).val ≠ 0 :=
      fun h => hgood ((real_injective_iff_gaps _).mpr h)
    simp only [not_forall, not_not] at hbad
    obtain ⟨p, hp⟩ := hbad
    obtain ⟨delta, hdelta, hloc⟩ := unique_crossing_isolated γ t₀ p hp
      (fun q hq => hunique t₀ q p hq hp)
    refine ⟨ball t₀ delta, isOpen_ball, mem_ball_self hdelta, Or.inr ⟨p, ?_, ?_⟩⟩
    · intro t ht he
      have hpos := (hloc t ht).1
      have hz : ((γ t).val p.val.1).im - ((γ t).val p.val.2).im = 0 := sub_eq_zero.mpr he
      rw [hz, mul_zero] at hpos
      exact (lt_irrefl 0) hpos
    · intro t ht k l hkl hex
      apply other_gaps_imply_separation (γ t).val p ?_ k l hkl hex
      intro q hqp hzero
      have hpos := (hloc t ht).2 q hqp
      rw [hzero, mul_zero] at hpos
      exact (lt_irrefl 0) hpos

def pairCrossingTimes {n : ℕ} (f : I → configurations n) : Set I :=
  {t | ∃ p : StrandPair n, realGap p (f t).val = 0}

lemma not_mem_pairCrossingTimes_iff {n : ℕ} (f : I → configurations n) (t : I) :
    t ∉ pairCrossingTimes f ↔ Function.Injective (fun k => ((f t).val k).re) := by
  simp only [pairCrossingTimes, mem_ofPred_eq, not_exists, real_injective_iff_gaps]

lemma affine_pairCrossingTimes_finite {n : ℕ} {a b : configurations n} (γ : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hγ : ∀ t : I, (γ t).val = AffineMap.lineMap a.val b.val (t : ℝ)) :
    (pairCrossingTimes γ).Finite := by
  have h := TarchaBraids.NormalForm.lineMap_crossings_finite_on a.val b.val ha (Icc 0 1)
  apply h.subset
  rintro t ⟨p, hp⟩
  refine ⟨p.val.1, p.val.2, ne_of_lt p.property, ?_⟩
  have he := sub_eq_zero.mp hp
  change ((γ t).val p.val.1).re = ((γ t).val p.val.2).re at he
  rw [hγ t] at he
  exact he

/-- Simple affine paths have a finite subdivision into local crossing charts,
with every vertex in a real-order chamber. -/
theorem simple_affine_chart_subdivision {n : ℕ} {a b : configurations n} (γ : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hγ : ∀ t : I, (γ t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (hunique : ∀ t (p q : StrandPair n), realGap p (γ t).val = 0 →
      realGap q (γ t).val = 0 → p = q) :
    ∃ (m : ℕ) (t : Fin (m + 1) → I),
      t 0 = 0 ∧ t (Fin.last m) = 1 ∧ StrictMono t ∧
      (∀ k, Function.Injective (fun j => ((γ (t k)).val j).re)) ∧
      ∀ k : Fin m, GoodChart (γ.subpath (t k.castSucc) (t k.succ)) univ := by
  classical
  choose U hU hmem hchart using exists_pair_chart γ hunique
  have hcover : univ ⊆ ⋃ s : I, U s := by
    intro s _
    exact mem_iUnion.mpr ⟨s, hmem s⟩
  have hT := affine_pairCrossingTimes_finite γ ha hγ
  have hT0 : (0 : I) ∉ pairCrossingTimes γ := by
    rw [not_mem_pairCrossingTimes_iff]
    simpa only [γ.source] using ha
  have hT1 : (1 : I) ∉ pairCrossingTimes γ := by
    rw [not_mem_pairCrossingTimes_iff]
    simpa only [γ.target] using hb
  obtain ⟨m, t, c, ht0, ht1, hmono, havoid, hsub⟩ :=
    finite_open_subdivision_avoiding U hU hcover hT hT0 hT1
  refine ⟨m, t, ht0, ht1, hmono, ?_, ?_⟩
  · intro k
    exact (not_mem_pairCrossingTimes_iff γ (t k)).mp (havoid k)
  · intro k
    have hle : t k.castSucc ≤ t k.succ := hmono.monotone (by
      change k.val ≤ k.val + 1
      omega)
    have hrange (s : I) : ∃ u ∈ U (c k), γ u = γ.subpath (t k.castSucc) (t k.succ) s := by
      have hr : γ.subpath (t k.castSucc) (t k.succ) s ∈
          γ '' Icc (t k.castSucc) (t k.succ) := by
        rw [← Path.range_subpath_of_le γ _ _ hle]
        exact ⟨s, rfl⟩
      obtain ⟨u, hu, he⟩ := hr
      exact ⟨u, hsub k hu, he⟩
    rcases hchart (c k) with hnone | ⟨p, him, hreal⟩
    · left
      intro s _
      obtain ⟨u, hu, he⟩ := hrange s
      rw [← he]
      exact hnone u hu
    · right
      refine ⟨p, ?_, ?_⟩
      · intro s _
        obtain ⟨u, hu, he⟩ := hrange s
        rw [← he]
        exact him u hu
      · intro s _ i j hij hex
        obtain ⟨u, hu, he⟩ := hrange s
        rw [← he]
        exact hreal u hu i j hij hex

end BraidNormalForm
end

/- PathWordAssembly -/
section
set_option autoImplicit false

namespace BraidNormalForm

noncomputable section

variable {X A : Type*} [TopologicalSpace X] {base : X}

/-- Algebraic word order, with the path order reversed. -/
def wordLoop (g : A → Path base base) : List A → Path base base
  | [] => Path.refl base
  | a :: w => (wordLoop g w).trans (g a)

theorem wordLoop_append (g : A → Path base base) (u v : List A) :
    (wordLoop g (u ++ v)).Homotopic ((wordLoop g v).trans (wordLoop g u)) := by
  apply Path.Homotopic.Quotient.eq.mp
  induction u with
  | nil =>
    simp only [List.nil_append, wordLoop, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl]
  | cons a u ih =>
    simp only [List.cons_append, wordLoop, Path.Homotopic.Quotient.mk_trans] at *
    rw [ih, Path.Homotopic.Quotient.trans_assoc]

def basedTrace {a b : X} (ca : Path base a) (p : Path a b) (cb : Path base b) :
    Path base base := ca.trans (p.trans cb.symm)

theorem basedTrace_trans {a b c : X} (ca : Path base a) (cb : Path base b)
    (cc : Path base c) (p : Path a b) (q : Path b c) :
    (basedTrace ca (p.trans q) cc).Homotopic
      ((basedTrace ca p cb).trans (basedTrace cb q cc)) := by
  apply Path.Homotopic.Quotient.eq.mp
  have hcancel : (Path.Homotopic.Quotient.mk cb).symm.trans
      ((Path.Homotopic.Quotient.mk cb).trans
        ((Path.Homotopic.Quotient.mk q).trans (Path.Homotopic.Quotient.mk cc).symm)) =
      (Path.Homotopic.Quotient.mk q).trans (Path.Homotopic.Quotient.mk cc).symm := by
    rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  simp only [basedTrace, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc,
    hcancel]

/-- Local signed-word descriptions telescope along any finite path subdivision.
The connector paths cancel, and the resulting list keeps algebraic word order. -/
theorem concat_has_word (g : A → Path base base) {m : ℕ}
    (v : Fin (m + 1) → X)
    (p : (k : Fin m) → Path (v k.castSucc) (v k.succ))
    (connect : (k : Fin (m + 1)) → Path base (v k))
    (hp : ∀ k, ∃ w : List A,
      (basedTrace (connect k.castSucc) (p k) (connect k.succ)).Homotopic (wordLoop g w)) :
    ∃ w : List A,
      (basedTrace (connect 0) (Path.concat v p) (connect (Fin.last m))).Homotopic
        (wordLoop g w) := by
  induction m with
  | zero =>
    refine ⟨[], ?_⟩
    rw [Path.concat_zero]
    change (basedTrace (connect 0) (Path.refl (v 0)) (connect 0)).Homotopic
      (Path.refl base)
    apply Path.Homotopic.Quotient.eq.mp
    simp only [basedTrace,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans,
      Path.Homotopic.Quotient.trans_symm]
  | succ m ih =>
    obtain ⟨u, hu⟩ := ih (v ∘ Fin.castSucc) (fun k => p k.castSucc)
      (fun k => connect k.castSucc) (fun k => hp k.castSucc)
    obtain ⟨w, hw⟩ := hp (Fin.last m)
    refine ⟨w ++ u, ?_⟩
    rw [Path.concat_succ]
    exact (basedTrace_trans (connect 0) (connect (Fin.last m).castSucc)
      (connect (Fin.last (m + 1))) _ _).trans
      ((hu.hcomp hw).trans (wordLoop_append g w u).symm)

end

end BraidNormalForm
end

/- CanonicalWordAssembly -/
section
set_option autoImplicit false

open BraidsLinksMCG

namespace TarchaBraids.NormalForm

theorem wordLoop_eq_braidWordLoop (n : ℕ) (w : List (BraidLetter n)) :
    BraidNormalForm.wordLoop (braidLetterLoop n) w = braidWordLoop n w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [BraidNormalForm.wordLoop, braidWordLoop, ih]

theorem concat_has_braid_word (n : ℕ) {m : ℕ}
    (v : Fin (m + 1) → UnorderedConfig n)
    (p : (k : Fin m) → Path (v k.castSucc) (v k.succ))
    (connect : (k : Fin (m + 1)) → Path (baseUnordered n) (v k))
    (hp : ∀ k, ∃ w : List (BraidLetter n),
      (BraidNormalForm.basedTrace (connect k.castSucc) (p k)
        (connect k.succ)).Homotopic (braidWordLoop n w)) :
    ∃ w : List (BraidLetter n),
      (BraidNormalForm.basedTrace (connect 0) (Path.concat v p)
        (connect (Fin.last m))).Homotopic (braidWordLoop n w) := by
  have hp' : ∀ k, ∃ w : List (BraidLetter n),
      (BraidNormalForm.basedTrace (connect k.castSucc) (p k)
        (connect k.succ)).Homotopic (BraidNormalForm.wordLoop (braidLetterLoop n) w) := by
    simpa only [wordLoop_eq_braidWordLoop] using hp
  simpa only [wordLoop_eq_braidWordLoop] using
    BraidNormalForm.concat_has_word (braidLetterLoop n) v p connect hp'

end TarchaBraids.NormalForm
end

/- ConfigurationCovering -/
section
namespace RebuiltConfigurationCovering
-- Prove2me | solution 1 for BraidsLinksMCG.configProj_isCoveringMap
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:54:59.315984+00:00
-- url     : https://prove2.me/submissions/5be6d908-554a-4774-b4bb-09c8a41323d9


set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace CovSol

/-- Relabelling action of the symmetric group on ordered configurations. -/
instance permAction (n : ℕ) : MulAction (Equiv.Perm (Fin n)) (OrderedConfig n) where
  smul g p := ⟨p.1 ∘ ⇑g⁻¹, p.2.comp (g⁻¹).injective⟩
  one_smul p := by apply Subtype.ext; funext i; rfl
  mul_smul g h p := by
    apply Subtype.ext
    funext i
    show p.1 ((g * h)⁻¹ i) = p.1 (h⁻¹ (g⁻¹ i))
    rw [mul_inv_rev]
    rfl

variable {n : ℕ}

lemma smul_val (g : Equiv.Perm (Fin n)) (p : OrderedConfig n) :
    (g • p).1 = p.1 ∘ ⇑g⁻¹ := rfl

instance : ContinuousConstSMul (Equiv.Perm (Fin n)) (OrderedConfig n) where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply (g⁻¹ i)).comp continuous_subtype_val

lemma proj_eq_iff (p q : OrderedConfig n) :
    configProj n p = configProj n q ↔ p ∈ MulAction.orbit (Equiv.Perm (Fin n)) q := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    refine ⟨g, ?_⟩
    apply Subtype.ext
    rw [smul_val, hg]
    funext i
    simp
  · rintro ⟨g, rfl⟩
    apply Quotient.sound
    refine ⟨g, ?_⟩
    funext i
    simp [smul_val]

/-- The action is free: a permutation fixing an injective tuple is the identity. -/
lemma smul_eq_self (p : OrderedConfig n) (g : Equiv.Perm (Fin n)) (h : g • p = p) : g = 1 := by
  have h1 : ∀ i, p.1 (g⁻¹ i) = p.1 i := fun i => congrFun (congrArg Subtype.val h) i
  have h2 : ∀ i, g⁻¹ i = i := fun i => p.2 (h1 i)
  have : g⁻¹ = 1 := Equiv.ext h2
  simpa using congrArg (·⁻¹) this

/-- Around any ordered configuration there is a neighbourhood whose translates by
nontrivial permutations miss it. -/
lemma disjoint_nbhd (e : OrderedConfig n) :
    ∃ U ∈ nhds e, ∀ g : Equiv.Perm (Fin n),
      (((g • ·) '' U) ∩ U).Nonempty → g = 1 := by
  classical
  have hsep : ∀ g : Equiv.Perm (Fin n), ∃ V W : Set (OrderedConfig n),
      IsOpen V ∧ IsOpen W ∧ e ∈ V ∧ g • e ∈ W ∧ (g ≠ 1 → Disjoint V W) := by
    intro g
    by_cases hg : g = 1
    · exact ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ, Set.mem_univ _, Set.mem_univ _,
        fun h => absurd hg h⟩
    · have hne : g • e ≠ e := fun h => hg (smul_eq_self e g h)
      obtain ⟨W', V', hW', hV', hgW', heV', hd⟩ := t2_separation hne
      exact ⟨V', W', hV', hW', heV', hgW', fun _ => hd.symm⟩
  choose V W hV hW heV hgW hdisj using hsep
  refine ⟨⋂ g : Equiv.Perm (Fin n), (V g ∩ ((g • ·) ⁻¹' (W g))), ?_, ?_⟩
  · refine IsOpen.mem_nhds ?_ ?_
    · exact isOpen_iInter_of_finite fun g =>
        (hV g).inter ((hW g).preimage (continuous_const_smul g))
    · exact Set.mem_iInter.mpr fun g => ⟨heV g, hgW g⟩
  · rintro g ⟨y, ⟨u, huU, rfl⟩, hguU⟩
    by_contra hne
    have h1 := Set.mem_iInter.mp huU g
    have h2 := Set.mem_iInter.mp hguU g
    exact Set.disjoint_left.mp (hdisj g hne) h2.1 h1.2

theorem configProj_isQuotientCovering (n : ℕ) :
    IsQuotientCoveringMap (⇑(configProj n)) (Equiv.Perm (Fin n)) where
  toIsQuotientMap := isQuotientMap_quotient_mk'
  toContinuousConstSMul := inferInstance
  apply_eq_iff_mem_orbit := proj_eq_iff _ _
  disjoint := disjoint_nbhd

theorem configProj_isCoveringMap (n : ℕ) : IsCoveringMap (configProj n) :=
  (configProj_isQuotientCovering n).isCoveringMap

end CovSol

theorem _root_.BraidsLinksMCG.configProj_isCoveringMap (n : ℕ) :
    IsCoveringMap (configProj n) :=
  CovSol.configProj_isCoveringMap n


end RebuiltConfigurationCovering
end

/- ConvexPathReplacement -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open unitInterval Set
open scoped Convex

noncomputable section

namespace BraidNormalForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} {a b : U}

theorem convex_paths_homotopic {C : Set E} (hC : Convex ℝ C) (hCU : C ⊆ U)
    (p q : Path a b) (hp : ∀ t : I, (p t).val ∈ C) (hq : ∀ t : I, (q t).val ∈ C) :
    p.Homotopic q := by
  have hmem (u t : I) : (p t).val + (u : ℝ) • ((q t).val - (p t).val) ∈ U := by
    apply hCU
    have h := hC (hp t) (hq t) (sub_nonneg.mpr u.property.2)
      u.property.1 (by ring : 1 - (u : ℝ) + (u : ℝ) = 1)
    convert h using 1
    module
  refine ⟨{
    toFun := fun x => ⟨(p x.2).val + (x.1 : ℝ) • ((q x.2).val - (p x.2).val), hmem x.1 x.2⟩
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_
  }⟩
  · intro t
    apply Subtype.ext
    simp
  · intro t
    apply Subtype.ext
    simp
  · intro u t ht
    rcases ht with (rfl | rfl)
    · apply Subtype.ext
      simp
    · apply Subtype.ext
      simp

def segmentIn (a b : U) (hs : segment ℝ a.val b.val ⊆ U) : Path a b where
  toFun t := ⟨Path.segment a.val b.val t, hs (by
    rw [← Path.range_segment]
    exact ⟨t, rfl⟩)⟩
  continuous_toFun := (Path.segment a.val b.val).continuous.subtype_mk _
  source' := by apply Subtype.ext; exact (Path.segment a.val b.val).source
  target' := by apply Subtype.ext; exact (Path.segment a.val b.val).target

lemma segmentIn_apply (a b : U) (hs : segment ℝ a.val b.val ⊆ U) (t : I) :
    (segmentIn a b hs t).val = AffineMap.lineMap a.val b.val (t : ℝ) := rfl

lemma segmentIn_mem {C : Set E} (hC : Convex ℝ C) (ha : a.val ∈ C) (hb : b.val ∈ C)
    (hs : segment ℝ a.val b.val ⊆ U) (t : I) : (segmentIn a b hs t).val ∈ C := by
  apply hC.segment_subset ha hb
  rw [← Path.range_segment]
  exact ⟨t, rfl⟩

theorem path_homotopic_segment {C : Set E} (hC : Convex ℝ C) (hCU : C ⊆ U)
    (p : Path a b) (hp : ∀ t : I, (p t).val ∈ C) :
    ∃ hs : segment ℝ a.val b.val ⊆ U, p.Homotopic (segmentIn a b hs) := by
  have ha : a.val ∈ C := by simpa only [p.source] using hp 0
  have hb : b.val ∈ C := by simpa only [p.target] using hp 1
  let hs : segment ℝ a.val b.val ⊆ U := (hC.segment_subset ha hb).trans hCU
  exact ⟨hs, convex_paths_homotopic hC hCU p (segmentIn a b hs) hp
    (segmentIn_mem hC ha hb hs)⟩

theorem polygonal_subpath_replacement (p : Path a b) {m : ℕ}
    (t : Fin (m + 1) → I) (C : Fin m → Set E)
    (hC : ∀ k, Convex ℝ (C k)) (hCU : ∀ k, C k ⊆ U)
    (hp : ∀ k s, (p.subpath (t k.castSucc) (t k.succ) s).val ∈ C k) :
    ∃ q : (k : Fin m) → Path (p (t k.castSucc)) (p (t k.succ)),
      (∀ k s, (q k s).val =
        AffineMap.lineMap (p (t k.castSucc)).val (p (t k.succ)).val (s : ℝ)) ∧
      (p.subpath (t 0) (t (Fin.last m))).Homotopic (Path.concat (p ∘ t) q) := by
  have h : ∀ k : Fin m, ∃ hs : segment ℝ (p (t k.castSucc)).val (p (t k.succ)).val ⊆ U,
      (p.subpath (t k.castSucc) (t k.succ)).Homotopic
        (segmentIn (p (t k.castSucc)) (p (t k.succ)) hs) :=
    fun k => path_homotopic_segment (hC k) (hCU k) _ (hp k)
  choose hs hh using h
  let q := fun k : Fin m => segmentIn (p (t k.castSucc)) (p (t k.succ)) (hs k)
  refine ⟨q, fun k s => segmentIn_apply _ _ _ s, ?_⟩
  exact (Path.Homotopic.concat_subpath p t).symm.trans
    (Path.Homotopic.concat_hcomp (p ∘ t)
      (fun k => p.subpath (t k.castSucc) (t k.succ)) q hh)

end BraidNormalForm

end
end

/- RealOrderChambers -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set unitInterval
open BraidsLinksMCG

noncomputable section

namespace BraidNormalForm

theorem exists_sorting_permutation {n : ℕ} (f : Fin n → ℝ)
    (hf : Function.Injective f) :
    ∃ perm : Equiv.Perm (Fin n), StrictMono (fun i => f (perm i)) := by
  let e : Fin n ≃ Set.range f := Equiv.ofInjective f hf
  let : Fintype (Set.range f) := Fintype.ofEquiv (Fin n) e
  have hcard : Fintype.card (Set.range f) = n :=
    (Fintype.card_congr e).symm.trans (Fintype.card_fin n)
  let o : Fin n ≃o Set.range f := Fintype.orderIsoFinOfCardEq (Set.range f) hcard
  let perm : Equiv.Perm (Fin n) := o.toEquiv.trans e.symm
  have he (i : Fin n) : f (perm i) = (o i).val :=
    congrArg Subtype.val (e.apply_symm_apply (o i))
  refine ⟨perm, ?_⟩
  intro i j hij
  change f (perm i) < f (perm j)
  rw [he, he]
  exact o.strictMono hij

theorem sorting_permutation_unique {n : ℕ} (f : Fin n → ℝ)
    {perm other : Equiv.Perm (Fin n)}
    (hperm : StrictMono (fun i => f (perm i))) (hother : StrictMono (fun i => f (other i))) :
    perm = other := by
  have hm : StrictMono (fun i => other.symm (perm i)) := by
    intro i j hij
    apply hother.lt_iff_lt.mp
    simpa only [Equiv.apply_symm_apply] using hperm hij
  apply Equiv.ext
  intro i
  have hi := congrArg other (hm.apply_eq (x := i))
  simpa only [Equiv.apply_symm_apply] using hi

def sortingPermutation {n : ℕ} (z : OrderedConfig n)
    (hz : Function.Injective (fun i => (z.val i).re)) : Equiv.Perm (Fin n) :=
  (exists_sorting_permutation _ hz).choose

theorem sortingPermutation_strictMono {n : ℕ} (z : OrderedConfig n)
    (hz : Function.Injective (fun i => (z.val i).re)) :
    StrictMono (fun i => (z.val (sortingPermutation z hz i)).re) :=
  (exists_sorting_permutation _ hz).choose_spec

def realChamber {n : ℕ} (perm : Equiv.Perm (Fin n)) : Set (Fin n → ℂ) :=
  {z | StrictMono (fun i => (z (perm i)).re)}

theorem realChamber_injective {n : ℕ} {perm : Equiv.Perm (Fin n)}
    {z : Fin n → ℂ} (hz : z ∈ realChamber perm) : Function.Injective z := by
  intro i j hij
  obtain ⟨i', rfl⟩ := perm.surjective i
  obtain ⟨j', rfl⟩ := perm.surjective j
  exact congrArg perm (hz.injective (congrArg Complex.re hij))

theorem realChamber_convex {n : ℕ} (perm : Equiv.Perm (Fin n)) :
    Convex ℝ (realChamber perm) := by
  intro x hx y hy a b ha hb hab i j hij
  have hx' := hx hij
  have hy' := hy hij
  simp only [Pi.add_apply, Pi.smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hax := mul_nonneg ha (sub_pos.mpr hx').le
  have hby := mul_nonneg hb (sub_pos.mpr hy').le
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hy'
  · have hax' := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (sub_pos.mpr hx')
    nlinarith

def relabelledBase {n : ℕ} (perm : Equiv.Perm (Fin n)) : OrderedConfig n :=
  ⟨(baseOrdered n).val ∘ perm.symm, (baseOrdered n).property.comp perm.symm.injective⟩

theorem relabelledBase_in_chamber {n : ℕ} (perm : Equiv.Perm (Fin n)) :
    (relabelledBase perm).val ∈ realChamber perm := by
  intro i j hij
  simpa only [relabelledBase, Function.comp_apply, Equiv.symm_apply_apply,
    baseOrdered, Complex.add_re, Complex.natCast_re, Complex.one_re,
    add_lt_add_iff_right, Nat.cast_lt] using (show (i : ℕ) < (j : ℕ) from hij)

theorem relabelledBase_projection {n : ℕ} (perm : Equiv.Perm (Fin n)) :
    configProj n (relabelledBase perm) = baseUnordered n := by
  symm
  apply Quotient.sound
  exact ⟨perm.symm, rfl⟩

def chamberApproach {n : ℕ} (perm : Equiv.Perm (Fin n)) (z : OrderedConfig n)
    (hz : z.val ∈ realChamber perm) : Path (relabelledBase perm) z :=
  segmentIn _ _ ((realChamber_convex perm).segment_subset
    (relabelledBase_in_chamber perm) hz |>.trans (fun _ h => realChamber_injective h))

theorem chamberApproach_in_chamber {n : ℕ} (perm : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : z.val ∈ realChamber perm) (t : I) :
    (chamberApproach perm z hz t).val ∈ realChamber perm :=
  segmentIn_mem (realChamber_convex perm) (relabelledBase_in_chamber perm) hz _ t

def unorderedChamberApproach {n : ℕ} (perm : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : z.val ∈ realChamber perm) :
    Path (baseUnordered n) (configProj n z) :=
  ((chamberApproach perm z hz).map (configProj n).continuous).cast
    (relabelledBase_projection perm).symm rfl

def canonicalChamberApproach {n : ℕ} (z : OrderedConfig n)
    (hz : Function.Injective (fun i => (z.val i).re)) :
    Path (baseUnordered n) (configProj n z) :=
  unorderedChamberApproach (sortingPermutation z hz) z (sortingPermutation_strictMono z hz)

theorem paths_in_chamber_homotopic {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a b : OrderedConfig n} (p q : Path a b)
    (hp : ∀ t : I, (p t).val ∈ realChamber perm)
    (hq : ∀ t : I, (q t).val ∈ realChamber perm) : p.Homotopic q :=
  convex_paths_homotopic (realChamber_convex perm)
    (fun _ h => realChamber_injective h) p q hp hq

end BraidNormalForm

end
end

/- CanonicalCrossingReference -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set unitInterval
open BraidsLinksMCG TarchaBraids

noncomputable section

namespace BraidNormalForm

def relabelConfig {n : ℕ} (perm : Equiv.Perm (Fin n)) :
    C(OrderedConfig n, OrderedConfig n) where
  toFun z := ⟨z.val ∘ perm, z.property.comp perm.injective⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun k => (continuous_apply (perm k)).comp continuous_subtype_val

theorem configProj_relabel {n : ℕ} (perm : Equiv.Perm (Fin n)) (z : OrderedConfig n) :
    configProj n (relabelConfig perm z) = configProj n z := by
  symm
  exact Quotient.sound ⟨perm, rfl⟩

def adjacentSwap {n : ℕ} (i : Fin (n - 1)) : Equiv.Perm (Fin n) :=
  Equiv.swap (strandIdx i) (strandIdxSucc i)

def referenceEnd (n : ℕ) (i : Fin (n - 1)) : OrderedConfig n := halfTwistConfig n i 1

theorem referenceEnd_relabel (n : ℕ) (i : Fin (n - 1)) :
    relabelConfig (adjacentSwap i) (referenceEnd n i) = baseOrdered n := by
  apply Subtype.ext
  exact (halfTwistConfig_one n i).symm

theorem relabel_base_referenceEnd (n : ℕ) (i : Fin (n - 1)) :
    relabelConfig (adjacentSwap i) (baseOrdered n) = referenceEnd n i := by
  apply Subtype.ext
  funext k
  have h := congrFun (halfTwistConfig_one n i) (adjacentSwap i k)
  change (baseOrdered n).val (adjacentSwap i k) = (halfTwistConfig n i 1).val k
  simpa only [Function.comp_apply, adjacentSwap, Equiv.swap_apply_self] using h

theorem referenceEnd_projection (n : ℕ) (i : Fin (n - 1)) :
    configProj n (referenceEnd n i) = baseUnordered n :=
  Quotient.sound ⟨adjacentSwap i, halfTwistConfig_one n i⟩

def positiveReference (n : ℕ) (i : Fin (n - 1)) :
    Path (baseOrdered n) (referenceEnd n i) where
  toFun t := halfTwistConfig n i (t : ℝ)
  continuous_toFun := (continuous_halfTwistConfig n i).comp continuous_subtype_val
  source' := halfTwistConfig_zero n i
  target' := rfl

def negativeReference (n : ℕ) (i : Fin (n - 1)) :
    Path (baseOrdered n) (referenceEnd n i) :=
  (((positiveReference n i).symm).map (relabelConfig (adjacentSwap i)).continuous).cast
    (referenceEnd_relabel n i).symm (relabel_base_referenceEnd n i).symm

theorem positiveReference_projection (n : ℕ) (i : Fin (n - 1)) :
    (((positiveReference n i).map (configProj n).continuous).cast
      rfl (referenceEnd_projection n i).symm) = halfTwistLoop n i := by
  apply Path.ext
  funext t
  rfl

theorem negativeReference_projection (n : ℕ) (i : Fin (n - 1)) :
    (((negativeReference n i).map (configProj n).continuous).cast
      rfl (referenceEnd_projection n i).symm) = (halfTwistLoop n i).symm := by
  apply Path.ext
  funext t
  exact configProj_relabel (adjacentSwap i) (positiveReference n i (unitInterval.symm t))

theorem positiveReference_imag_gap (n : ℕ) (i : Fin (n - 1)) (t : I) :
    (((positiveReference n i t).val (strandIdxSucc i)).im -
      ((positiveReference n i t).val (strandIdx i)).im) = Real.sin (Real.pi * (t : ℝ)) := by
  change (halfTwistFun n i (t : ℝ) (strandIdxSucc i)).im -
    (halfTwistFun n i (t : ℝ) (strandIdx i)).im = _
  rw [halfTwistFun_of_eq_succ (t : ℝ) (by simp [strandIdxSucc]) (by simp [strandIdxSucc]),
    halfTwistFun_of_eq (t : ℝ) (by simp [strandIdx]), twistPoint_im, twistPoint_im]
  ring

theorem positiveReference_imag_pos (n : ℕ) (i : Fin (n - 1)) (t : I)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    0 < (((positiveReference n i t).val (strandIdxSucc i)).im -
      ((positiveReference n i t).val (strandIdx i)).im) := by
  rw [positiveReference_imag_gap]
  have h0 : 0 < (t : ℝ) := unitInterval.pos_iff_ne_zero.mpr ht0
  have h1 : (t : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr ht1
  exact Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0)
    (by simpa only [mul_one] using mul_lt_mul_of_pos_left h1 Real.pi_pos)

theorem negativeReference_imag_neg (n : ℕ) (i : Fin (n - 1)) (t : I)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    0 < (-1 : ℝ) * (((negativeReference n i t).val (strandIdxSucc i)).im -
      ((negativeReference n i t).val (strandIdx i)).im) := by
  have h := positiveReference_imag_pos n i (unitInterval.symm t)
    (fun he => ht1 (unitInterval.symm_eq_zero.mp he))
    (fun he => ht0 (unitInterval.symm_eq_one.mp he))
  change 0 < (-1 : ℝ) *
    (((positiveReference n i (unitInterval.symm t)).val
        (adjacentSwap i (strandIdxSucc i))).im -
      ((positiveReference n i (unitInterval.symm t)).val
        (adjacentSwap i (strandIdx i))).im)
  simp only [adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right]
  linarith

end BraidNormalForm

end
end

/- ChamberRelabeling -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG

namespace BraidNormalForm

theorem relabel_in_chamber {n : ℕ} (perm order : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : z.val ∈ realChamber order) :
    (relabelConfig perm z).val ∈ realChamber (order.trans perm.symm) := by
  intro i j hij
  change (z.val (perm (perm.symm (order i)))).re < (z.val (perm (perm.symm (order j)))).re
  simpa only [Equiv.apply_symm_apply] using hz hij

theorem chamberApproach_relabel {n : ℕ} (perm order : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : z.val ∈ realChamber order) (t : I) :
    chamberApproach (order.trans perm.symm) (relabelConfig perm z)
      (relabel_in_chamber perm order z hz) t =
      relabelConfig perm (chamberApproach order z hz t) := by
  apply Subtype.ext
  funext k
  rfl

theorem unorderedChamberApproach_relabel {n : ℕ} (perm order : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : z.val ∈ realChamber order) :
    ((unorderedChamberApproach (order.trans perm.symm) (relabelConfig perm z)
      (relabel_in_chamber perm order z hz)).cast rfl (configProj_relabel perm z).symm) =
      unorderedChamberApproach order z hz := by
  apply Path.ext
  funext t
  change configProj n (chamberApproach (order.trans perm.symm) (relabelConfig perm z)
    (relabel_in_chamber perm order z hz) t) = configProj n (chamberApproach order z hz t)
  rw [chamberApproach_relabel, configProj_relabel]

theorem relabel_real_injective {n : ℕ} (perm : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : Function.Injective (fun i => (z.val i).re)) :
    Function.Injective (fun i => ((relabelConfig perm z).val i).re) :=
  hz.comp perm.injective

theorem sortingPermutation_relabel {n : ℕ} (perm : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : Function.Injective (fun i => (z.val i).re)) :
    sortingPermutation (relabelConfig perm z) (relabel_real_injective perm z hz) =
      (sortingPermutation z hz).trans perm.symm := by
  apply sorting_permutation_unique (fun i => ((relabelConfig perm z).val i).re)
    (sortingPermutation_strictMono _ _)
  exact relabel_in_chamber perm (sortingPermutation z hz) z
    (sortingPermutation_strictMono z hz)

theorem canonicalChamberApproach_relabel {n : ℕ} (perm : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : Function.Injective (fun i => (z.val i).re)) :
    ((canonicalChamberApproach (relabelConfig perm z) (relabel_real_injective perm z hz)).cast
      rfl (configProj_relabel perm z).symm) = canonicalChamberApproach z hz := by
  have hperm := sortingPermutation_relabel perm z hz
  apply Path.ext
  funext t
  apply Quotient.sound
  refine ⟨perm.symm, ?_⟩
  funext k
  change (AffineMap.lineMap (relabelledBase (sortingPermutation z hz)).val z.val (t : ℝ)) k =
    (AffineMap.lineMap
      (relabelledBase (sortingPermutation (relabelConfig perm z)
        (relabel_real_injective perm z hz))).val (relabelConfig perm z).val (t : ℝ)) (perm.symm k)
  rw [hperm]
  simp [AffineMap.lineMap_apply_module, relabelledBase, relabelConfig, Function.comp_def]

end BraidNormalForm
end

/- NoCrossingChamber -/
section
set_option autoImplicit false

open Set unitInterval
open BraidsLinksMCG

namespace BraidNormalForm

theorem real_order_constant {f g : I → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hne : ∀ t, f t ≠ g t) (h0 : f 0 < g 0) : ∀ t, f t < g t := by
  intro t
  by_contra ht
  have hh : Continuous (fun u => g u - f u) := hg.sub hf
  have hmem : 0 ∈ Set.Icc (g t - f t) (g 0 - f 0) :=
    ⟨sub_nonpos.mpr (le_of_not_gt ht), (sub_pos.mpr h0).le⟩
  obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hh hmem
  exact hne u (sub_eq_zero.mp hu).symm

theorem no_crossing_path_in_chamber {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a b : OrderedConfig n} (p : Path a b)
    (ha : a.val ∈ realChamber perm)
    (hreal : ∀ t : I, Function.Injective (fun i => ((p t).val i).re)) :
    ∀ t : I, (p t).val ∈ realChamber perm := by
  intro t i j hij
  have hne : ∀ u : I, ((p u).val (perm i)).re ≠ ((p u).val (perm j)).re := by
    intro u he
    exact (ne_of_lt hij) (perm.injective (hreal u he))
  have h0 : ((p 0).val (perm i)).re < ((p 0).val (perm j)).re := by
    simpa only [p.source] using ha hij
  have hf : Continuous (fun u : I => ((p u).val (perm i)).re) :=
    Complex.continuous_re.comp ((continuous_apply (perm i)).comp
      (continuous_subtype_val.comp p.continuous))
  have hg : Continuous (fun u : I => ((p u).val (perm j)).re) :=
    Complex.continuous_re.comp ((continuous_apply (perm j)).comp
      (continuous_subtype_val.comp p.continuous))
  exact real_order_constant hf hg hne h0 t

/-- Inside a real-order chamber, every path agrees with the route through its
chosen relabelled base configuration. -/
theorem chamber_path_comparison {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a b : OrderedConfig n} (p : Path a b)
    (ha : a.val ∈ realChamber perm) (hb : b.val ∈ realChamber perm)
    (hp : ∀ t : I, (p t).val ∈ realChamber perm) :
    p.Homotopic ((chamberApproach perm a ha).symm.trans (chamberApproach perm b hb)) := by
  apply paths_in_chamber_homotopic perm p _ hp
  let S : Set (OrderedConfig n) := {z | z.val ∈ realChamber perm}
  have hleft : Set.range (chamberApproach perm a ha).symm ⊆ S := by
    rw [Path.symm_range]
    rintro _ ⟨t, rfl⟩
    exact chamberApproach_in_chamber perm a ha t
  have hright : Set.range (chamberApproach perm b hb) ⊆ S := by
    rintro _ ⟨t, rfl⟩
    exact chamberApproach_in_chamber perm b hb t
  have hboth : Set.range ((chamberApproach perm a ha).symm.trans
      (chamberApproach perm b hb)) ⊆ S := by
    rw [Path.trans_range]
    exact Set.union_subset hleft hright
  intro t
  exact hboth ⟨t, rfl⟩

end BraidNormalForm
end

/- ProjectedChamberTrace -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG

namespace BraidNormalForm

theorem map_basedTrace_cast {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {base a b : X} (ca : Path base a) (p : Path a b) (cb : Path base b)
    {f : X → Y} (hf : Continuous f) {base' : Y} (hbase : base' = f base) :
    ((basedTrace ca p cb).map hf).cast hbase hbase =
      basedTrace ((ca.map hf).cast hbase rfl) (p.map hf) ((cb.map hf).cast hbase rfl) := by
  have h₁ := Path.map_trans ca (p.trans cb.symm) hf
  have h₂ := Path.map_trans p cb.symm hf
  have h₃ := h₁.trans (congrArg (fun γ => (ca.map hf).trans γ) h₂)
  exact (congrArg (fun γ => γ.cast hbase hbase) h₃).trans rfl

theorem ordered_chamber_trace_null {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a b : OrderedConfig n} (p : Path a b)
    (ha : a.val ∈ realChamber perm) (hb : b.val ∈ realChamber perm)
    (hp : ∀ t : I, (p t).val ∈ realChamber perm) :
    (basedTrace (chamberApproach perm a ha) p (chamberApproach perm b hb)).Homotopic
      (Path.refl (relabelledBase perm)) := by
  have h := (Path.Homotopic.refl (chamberApproach perm a ha)).hcomp
    ((chamber_path_comparison perm p ha hb hp).hcomp
      (Path.Homotopic.refl (chamberApproach perm b hb).symm))
  apply Path.Homotopic.Quotient.eq.mp
  have he := Path.Homotopic.Quotient.eq.mpr h
  simpa only [basedTrace, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] using he

theorem unordered_chamber_trace_null {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a b : OrderedConfig n} (p : Path a b)
    (ha : a.val ∈ realChamber perm) (hb : b.val ∈ realChamber perm)
    (hp : ∀ t : I, (p t).val ∈ realChamber perm) :
    (basedTrace (unorderedChamberApproach perm a ha)
      (p.map (configProj n).continuous) (unorderedChamberApproach perm b hb)).Homotopic
      (Path.refl (baseUnordered n)) := by
  have h := ((ordered_chamber_trace_null perm p ha hb hp).map (configProj n)).pathCast
    (relabelledBase_projection perm).symm (relabelledBase_projection perm).symm
  have he := map_basedTrace_cast (chamberApproach perm a ha) p
    (chamberApproach perm b hb) (configProj n).continuous
    (relabelledBase_projection perm).symm
  have href : (((Path.refl (relabelledBase perm)).map (configProj n).continuous).cast
      (relabelledBase_projection perm).symm (relabelledBase_projection perm).symm) =
      Path.refl (baseUnordered n) := by
    apply Path.ext
    funext t
    exact relabelledBase_projection perm
  rw [href] at h
  exact Eq.mp (congrArg (fun γ => γ.Homotopic (Path.refl (baseUnordered n))) he) h

end BraidNormalForm
end

/- SingleCrossingSquare -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set unitInterval

namespace BraidNormalForm

private lemma weighted_positive (u : I) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < (1 - (u : ℝ)) * x + (u : ℝ) * y := by
  by_cases hu : (u : ℝ) = 1
  · simpa only [hu, sub_self, zero_mul, one_mul, zero_add] using hy
  have hlt : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 hu
  have hfirst := mul_pos (sub_pos.mpr hlt) hx
  have hsecond := mul_nonneg u.property.1 hy.le
  linarith

private def crossingBlend {n : ℕ} (p q : I → configurations n) (u t : I) : Fin n → ℂ :=
  fun k => ⟨(1 - (u : ℝ)) * ((p t).val k).re + (u : ℝ) * ((q t).val k).re,
    (1 - (u : ℝ)) * ((p t).val k).im + (u : ℝ) * ((q t).val k).im⟩

/-- A square joining two single-crossing models. All other pairs remain
strictly ordered in their real coordinates. The selected pair is protected by
its signed imaginary separation in the time interior and by real separation
at the two endpoints. Consequently the whole interpolation avoids collisions.
The hypotheses are explicit and will be established on isolated affine
crossing intervals and for the signed canonical half-twist. -/
theorem single_crossing_square {n : ℕ} {a b c d : configurations n}
    (p : Path a b) (q : Path c d) (i j : Fin n) (sign : ℝ)
    (hpOrder : ∀ (t : I) (k l : Fin n), k < l → (k ≠ i ∨ l ≠ j) →
      ((p t).val k).re < ((p t).val l).re)
    (hqOrder : ∀ (t : I) (k l : Fin n), k < l → (k ≠ i ∨ l ≠ j) →
      ((q t).val k).re < ((q t).val l).re)
    (hpImag : ∀ t : I, 0 < sign * (((p t).val j).im - ((p t).val i).im))
    (hqImag : ∀ t : I, t ≠ 0 → t ≠ 1 →
      0 < sign * (((q t).val j).im - ((q t).val i).im))
    (hpStart : (a.val i).re < (a.val j).re)
    (hqStart : (c.val i).re < (c.val j).re)
    (hpEnd : (b.val j).re < (b.val i).re)
    (hqEnd : (d.val j).re < (d.val i).re) :
    ∃ H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap,
      (∀ (u t : I) (k : Fin n), ((H (u, t)).val k).re =
        (1 - (u : ℝ)) * ((p t).val k).re + (u : ℝ) * ((q t).val k).re) ∧
      (∀ (u t : I) (k : Fin n), ((H (u, t)).val k).im =
        (1 - (u : ℝ)) * ((p t).val k).im + (u : ℝ) * ((q t).val k).im) := by
  have hinj (u t : I) : Function.Injective (crossingBlend p q u t) := by
    have hsep (k l : Fin n) (hkl : k < l) :
        crossingBlend p q u t k ≠ crossingBlend p q u t l := by
      intro he
      by_cases hpair : k = i ∧ l = j
      · rcases hpair with ⟨hk, hl⟩
        subst k
        subst l
        by_cases ht0 : t = 0
        · subst t
          have hpos := weighted_positive u (sub_pos.mpr hpStart) (sub_pos.mpr hqStart)
          have hre := congrArg Complex.re he
          simp only [crossingBlend, p.source, q.source] at hre
          nlinarith [hpos]
        by_cases ht1 : t = 1
        · subst t
          have hpos := weighted_positive u (sub_pos.mpr hpEnd) (sub_pos.mpr hqEnd)
          have hre := congrArg Complex.re he
          simp only [crossingBlend, p.target, q.target] at hre
          nlinarith [hpos]
        have hpos := weighted_positive u (hpImag t) (hqImag t ht0 ht1)
        have him := congrArg Complex.im he
        change (1 - (u : ℝ)) * ((p t).val i).im + (u : ℝ) * ((q t).val i).im =
          (1 - (u : ℝ)) * ((p t).val j).im + (u : ℝ) * ((q t).val j).im at him
        have he' := congrArg (fun x : ℝ => sign * x) him
        nlinarith [hpos, he']
      · have hnot : k ≠ i ∨ l ≠ j := by tauto
        have hpos := weighted_positive u
          (sub_pos.mpr (hpOrder t k l hkl hnot)) (sub_pos.mpr (hqOrder t k l hkl hnot))
        have hre := congrArg Complex.re he
        change (1 - (u : ℝ)) * ((p t).val k).re + (u : ℝ) * ((q t).val k).re =
          (1 - (u : ℝ)) * ((p t).val l).re + (u : ℝ) * ((q t).val l).re at hre
        nlinarith [hpos]
    intro k l he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hsep k l hlt he
    · exact hsep l k hgt he.symm
  have hpcont : Continuous (fun t : I => (p t).val) :=
    continuous_subtype_val.comp p.continuous
  have hqcont : Continuous (fun t : I => (q t).val) :=
    continuous_subtype_val.comp q.continuous
  let H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap := {
    toFun := fun x => ⟨crossingBlend p q x.1 x.2, hinj x.1 x.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      have hpc : Continuous (fun x : I × I => (p x.2).val k) :=
        (continuous_apply k).comp (hpcont.comp continuous_snd)
      have hqc : Continuous (fun x : I × I => (q x.2).val k) :=
        (continuous_apply k).comp (hqcont.comp continuous_snd)
      unfold crossingBlend
      simp only [Complex.mk_eq_add_mul_I]
      have hu : Continuous (fun x : I × I => (x.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact (Complex.continuous_ofReal.comp
        (((continuous_const.sub hu).mul (Complex.continuous_re.comp hpc)).add
          (hu.mul (Complex.continuous_re.comp hqc)))).add
        ((Complex.continuous_ofReal.comp
          (((continuous_const.sub hu).mul (Complex.continuous_im.comp hpc)).add
            (hu.mul (Complex.continuous_im.comp hqc)))).mul continuous_const)
    map_zero_left := by
      intro t
      apply Subtype.ext
      funext k
      apply Complex.ext <;> simp [crossingBlend]
    map_one_left := by
      intro t
      apply Subtype.ext
      funext k
      apply Complex.ext <;> simp [crossingBlend]
  }
  exact ⟨H, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end BraidNormalForm
end

/- CanonicalCrossingOrder -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open unitInterval
open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

theorem adjacent_interval_order {n : ℕ} (i : Fin (n - 1)) (f : Fin n → ℝ)
    (hleft : (i.val : ℝ) + 1 ≤ f (strandIdx i) ∧ f (strandIdx i) ≤ (i.val : ℝ) + 2)
    (hright : (i.val : ℝ) + 1 ≤ f (strandIdxSucc i) ∧
      f (strandIdxSucc i) ≤ (i.val : ℝ) + 2)
    (hfixed : ∀ k, k ≠ strandIdx i → k ≠ strandIdxSucc i → f k = (k.val : ℝ) + 1)
    (k l : Fin n) (hkl : k < l) (hex : k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) :
    f k < f l := by
  have hklN : k.val < l.val := hkl
  have hkN : (strandIdx i).val = i.val := rfl
  have hlN : (strandIdxSucc i).val = i.val + 1 := rfl
  by_cases hk : k = strandIdx i ∨ k = strandIdxSucc i
  · by_cases hl : l = strandIdx i ∨ l = strandIdxSucc i
    · rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
      · exact False.elim ((lt_irrefl _ hkl))
      · exact False.elim (by simp at hex)
      · exact False.elim (by simp only [hkN, hlN] at hklN; omega)
      · exact False.elim ((lt_irrefl _ hkl))
    · have hl0 : l ≠ strandIdx i := fun h => hl (Or.inl h)
      have hl1 : l ≠ strandIdxSucc i := fun h => hl (Or.inr h)
      have hln0 : l.val ≠ i.val := fun h => hl0 (Fin.ext h)
      have hln1 : l.val ≠ i.val + 1 := fun h => hl1 (Fin.ext h)
      have hkn : k.val = i.val ∨ k.val = i.val + 1 := by
        rcases hk with h | h
        · exact Or.inl ((congrArg Fin.val h).trans hkN)
        · exact Or.inr ((congrArg Fin.val h).trans hlN)
      have hln : i.val + 2 ≤ l.val := by omega
      have hlnR : (i.val : ℝ) + 2 ≤ (l.val : ℝ) := by exact_mod_cast hln
      rw [hfixed l hl0 hl1]
      rcases hk with rfl | rfl <;> linarith [hleft.2, hright.2]
  · have hk0 : k ≠ strandIdx i := fun h => hk (Or.inl h)
    have hk1 : k ≠ strandIdxSucc i := fun h => hk (Or.inr h)
    by_cases hl : l = strandIdx i ∨ l = strandIdxSucc i
    · have hkn0 : k.val ≠ i.val := fun h => hk0 (Fin.ext h)
      have hkn1 : k.val ≠ i.val + 1 := fun h => hk1 (Fin.ext h)
      have hln : l.val = i.val ∨ l.val = i.val + 1 := by
        rcases hl with h | h
        · exact Or.inl ((congrArg Fin.val h).trans hkN)
        · exact Or.inr ((congrArg Fin.val h).trans hlN)
      have hkn : k.val + 1 ≤ i.val := by omega
      have hknR : (k.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hkn
      rw [hfixed k hk0 hk1]
      rcases hl with rfl | rfl <;> linarith [hleft.1, hright.1]
    · rw [hfixed k hk0 hk1, hfixed l (fun h => hl (Or.inl h)) (fun h => hl (Or.inr h))]
      exact_mod_cast Nat.add_lt_add_right hklN 1

theorem positiveReference_real_order (n : ℕ) (i : Fin (n - 1)) (t : I)
    (k l : Fin n) (hkl : k < l) (hex : k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) :
    ((positiveReference n i t).val k).re < ((positiveReference n i t).val l).re := by
  apply adjacent_interval_order i (fun k => ((positiveReference n i t).val k).re) ?_ ?_ ?_ k l hkl hex
  · change (i.val : ℝ) + 1 ≤ (halfTwistFun n i (t : ℝ) (strandIdx i)).re ∧
      (halfTwistFun n i (t : ℝ) (strandIdx i)).re ≤ (i.val : ℝ) + 2
    rw [halfTwistFun_of_eq (t : ℝ) (by simp [strandIdx]), twistPoint_re]
    constructor <;> nlinarith [Real.neg_one_le_cos (Real.pi * (t : ℝ)), Real.cos_le_one (Real.pi * (t : ℝ))]
  · change (i.val : ℝ) + 1 ≤ (halfTwistFun n i (t : ℝ) (strandIdxSucc i)).re ∧
      (halfTwistFun n i (t : ℝ) (strandIdxSucc i)).re ≤ (i.val : ℝ) + 2
    rw [halfTwistFun_of_eq_succ (t : ℝ) (by simp [strandIdxSucc]) (by simp [strandIdxSucc]), twistPoint_re]
    constructor <;> nlinarith [Real.neg_one_le_cos (Real.pi * (t : ℝ)), Real.cos_le_one (Real.pi * (t : ℝ))]
  · intro k hk0 hk1
    change (halfTwistFun n i (t : ℝ) k).re = _
    rw [halfTwistFun_of_fixed (t : ℝ) (fun h => hk0 (Fin.ext h)) (fun h => hk1 (Fin.ext h))]
    rfl

theorem negativeReference_real_order (n : ℕ) (i : Fin (n - 1)) (t : I)
    (k l : Fin n) (hkl : k < l) (hex : k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) :
    ((negativeReference n i t).val k).re < ((negativeReference n i t).val l).re := by
  have he (k : Fin n) : (negativeReference n i t).val k =
      halfTwistFun n i ((unitInterval.symm t : I) : ℝ) (adjacentSwap i k) := rfl
  apply adjacent_interval_order i (fun k => ((negativeReference n i t).val k).re) ?_ ?_ ?_ k l hkl hex
  · rw [he, adjacentSwap, Equiv.swap_apply_left]
    rw [halfTwistFun_of_eq_succ ((unitInterval.symm t : I) : ℝ)
      (by simp [strandIdxSucc]) (by simp [strandIdxSucc]), twistPoint_re]
    constructor <;> nlinarith [Real.neg_one_le_cos (Real.pi * ((unitInterval.symm t : I) : ℝ)),
      Real.cos_le_one (Real.pi * ((unitInterval.symm t : I) : ℝ))]
  · rw [he, adjacentSwap, Equiv.swap_apply_right]
    rw [halfTwistFun_of_eq ((unitInterval.symm t : I) : ℝ) (by simp [strandIdx]), twistPoint_re]
    constructor <;> nlinarith [Real.neg_one_le_cos (Real.pi * ((unitInterval.symm t : I) : ℝ)),
      Real.cos_le_one (Real.pi * ((unitInterval.symm t : I) : ℝ))]
  · intro k hk0 hk1
    rw [he, adjacentSwap, Equiv.swap_apply_of_ne_of_ne hk0 hk1]
    rw [halfTwistFun_of_fixed ((unitInterval.symm t : I) : ℝ)
      (fun h => hk0 (Fin.ext h)) (fun h => hk1 (Fin.ext h))]
    rfl

theorem reference_start_order (n : ℕ) (i : Fin (n - 1)) :
    ((baseOrdered n).val (strandIdx i)).re < ((baseOrdered n).val (strandIdxSucc i)).re := by
  simp only [baseOrdered, strandIdx, strandIdxSucc, Complex.add_re, Complex.natCast_re,
    Complex.one_re, Nat.cast_add, Nat.cast_one]
  linarith

theorem reference_end_order (n : ℕ) (i : Fin (n - 1)) :
    ((referenceEnd n i).val (strandIdxSucc i)).re <
      ((referenceEnd n i).val (strandIdx i)).re := by
  have h := congrArg Subtype.val (referenceEnd_relabel n i)
  have hi := congrFun h (strandIdx i)
  have hj := congrFun h (strandIdxSucc i)
  change (referenceEnd n i).val (adjacentSwap i (strandIdx i)) =
    (baseOrdered n).val (strandIdx i) at hi
  change (referenceEnd n i).val (adjacentSwap i (strandIdxSucc i)) =
    (baseOrdered n).val (strandIdxSucc i) at hj
  simp only [adjacentSwap, Equiv.swap_apply_left] at hi
  simp only [adjacentSwap, Equiv.swap_apply_right] at hj
  rw [hi, hj]
  exact reference_start_order n i

end BraidNormalForm
end

/- CanonicalSingleCrossingSquare -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open unitInterval BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

def LinearSquare {n : ℕ} {a b c d : OrderedConfig n} (p : Path a b) (q : Path c d)
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap) : Prop :=
  (∀ (u t : I) (k : Fin n), ((H (u, t)).val k).re =
    (1 - (u : ℝ)) * ((p t).val k).re + (u : ℝ) * ((q t).val k).re) ∧
  (∀ (u t : I) (k : Fin n), ((H (u, t)).val k).im =
    (1 - (u : ℝ)) * ((p t).val k).im + (u : ℝ) * ((q t).val k).im)

theorem positive_crossing_square {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (i : Fin (n - 1))
    (hpOrder : ∀ (t : I) (k l : Fin n), k < l →
      (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      ((p t).val k).re < ((p t).val l).re)
    (hpImag : ∀ t : I, 0 < ((p t).val (strandIdxSucc i)).im -
      ((p t).val (strandIdx i)).im)
    (hpStart : (a.val (strandIdx i)).re < (a.val (strandIdxSucc i)).re)
    (hpEnd : (b.val (strandIdxSucc i)).re < (b.val (strandIdx i)).re) :
    ∃ H : ContinuousMap.Homotopy p.toContinuousMap (positiveReference n i).toContinuousMap,
      LinearSquare p (positiveReference n i) H := by
  exact single_crossing_square p (positiveReference n i) (strandIdx i) (strandIdxSucc i) 1
    hpOrder (positiveReference_real_order n i)
    (fun t => by rw [one_mul]; exact hpImag t)
    (fun t h0 h1 => by rw [one_mul]; exact positiveReference_imag_pos n i t h0 h1)
    hpStart (reference_start_order n i) hpEnd (reference_end_order n i)

theorem negative_crossing_square {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (i : Fin (n - 1))
    (hpOrder : ∀ (t : I) (k l : Fin n), k < l →
      (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      ((p t).val k).re < ((p t).val l).re)
    (hpImag : ∀ t : I, ((p t).val (strandIdxSucc i)).im -
      ((p t).val (strandIdx i)).im < 0)
    (hpStart : (a.val (strandIdx i)).re < (a.val (strandIdxSucc i)).re)
    (hpEnd : (b.val (strandIdxSucc i)).re < (b.val (strandIdx i)).re) :
    ∃ H : ContinuousMap.Homotopy p.toContinuousMap (negativeReference n i).toContinuousMap,
      LinearSquare p (negativeReference n i) H := by
  exact single_crossing_square p (negativeReference n i) (strandIdx i) (strandIdxSucc i) (-1)
    hpOrder (negativeReference_real_order n i)
    (fun t => by rw [neg_one_mul]; exact neg_pos.mpr (hpImag t))
    (negativeReference_imag_neg n i)
    hpStart (reference_start_order n i) hpEnd (reference_end_order n i)

end BraidNormalForm
end

/- PathHomotopyBoundary -/
section
set_option autoImplicit false

namespace BraidNormalForm

/-- A homotopy square expresses the initial path by its two endpoint tracks
and the final path. The endpoints of the initial path need not coincide. -/
theorem path_map_homotopic_conjugate {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (F : f.Homotopy g) {x y : X} (p : Path x y) :
    (p.map f.continuous).Homotopic
      ((F.evalAt x).trans ((p.map g.continuous).trans (F.evalAt y).symm)) := by
  apply Path.Homotopic.Quotient.eq.mp
  have h := (Path.Homotopic.map_trans_evalAt F p).hcomp
    (Path.Homotopic.refl (F.evalAt y).symm)
  have he := Path.Homotopic.Quotient.eq.mpr h
  simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] using he

end BraidNormalForm
end

/- PathSquareBoundary -/
section
set_option autoImplicit false

open unitInterval

namespace BraidNormalForm

noncomputable section

variable {X : Type*} [TopologicalSpace X] {a b c d : X}
variable (p : Path a b) (q : Path c d)

def squareLeft (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap) : Path a c :=
  (H.evalAt 0).cast p.source.symm q.source.symm

def squareRight (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap) : Path b d :=
  (H.evalAt 1).cast p.target.symm q.target.symm

theorem path_square_boundary
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap) :
    p.Homotopic ((squareLeft p q H).trans (q.trans (squareRight p q H).symm)) := by
  have h := (path_map_homotopic_conjugate H unitInterval.path01).pathCast
    p.source.symm p.target.symm
  have hleft : ((unitInterval.path01.map p.continuous).cast p.source.symm p.target.symm) = p := by
    apply Path.ext
    funext t
    rfl
  have hright : (((H.evalAt 0).trans
      ((unitInterval.path01.map q.continuous).trans (H.evalAt 1).symm)).cast
        p.source.symm p.target.symm) =
      (squareLeft p q H).trans (q.trans (squareRight p q H).symm) := by
    apply Path.ext
    funext t
    rfl
  rw [hleft, hright] at h
  exact h

end

end BraidNormalForm
end

/- ChamberConnectorComposition -/
section
set_option autoImplicit false

open Set unitInterval
open BraidsLinksMCG

namespace BraidNormalForm

theorem chamberApproach_trans_homotopic {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a b : OrderedConfig n} (p : Path a b)
    (ha : a.val ∈ realChamber perm) (hb : b.val ∈ realChamber perm)
    (hp : ∀ t : I, (p t).val ∈ realChamber perm) :
    ((chamberApproach perm a ha).trans p).Homotopic (chamberApproach perm b hb) := by
  apply paths_in_chamber_homotopic perm
  · let S : Set (OrderedConfig n) := {z | z.val ∈ realChamber perm}
    have hl : Set.range (chamberApproach perm a ha) ⊆ S := by
      rintro _ ⟨t, rfl⟩
      exact chamberApproach_in_chamber perm a ha t
    have hr : Set.range p ⊆ S := by
      rintro _ ⟨t, rfl⟩
      exact hp t
    have hboth : Set.range ((chamberApproach perm a ha).trans p) ⊆ S := by
      rw [Path.trans_range]
      exact Set.union_subset hl hr
    intro t
    exact hboth ⟨t, rfl⟩
  · exact chamberApproach_in_chamber perm b hb

theorem unorderedChamberApproach_trans_homotopic {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a b : OrderedConfig n} (p : Path a b)
    (ha : a.val ∈ realChamber perm) (hb : b.val ∈ realChamber perm)
    (hp : ∀ t : I, (p t).val ∈ realChamber perm) :
    ((unorderedChamberApproach perm a ha).trans (p.map (configProj n).continuous)).Homotopic
      (unorderedChamberApproach perm b hb) := by
  have h := ((chamberApproach_trans_homotopic perm p ha hb hp).map (configProj n)).pathCast
    (relabelledBase_projection perm).symm rfl
  have he := congrArg (fun γ => γ.cast (relabelledBase_projection perm).symm rfl)
    (Path.map_trans (chamberApproach perm a ha) p (configProj n).continuous)
  rw [he] at h
  exact h

theorem linear_square_mem_chamber {n : ℕ} {a b c d : OrderedConfig n}
    (p : Path a b) (q : Path c d)
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (hreal : ∀ (u t : I) (k : Fin n), ((H (u, t)).val k).re =
      (1 - (u : ℝ)) * ((p t).val k).re + (u : ℝ) * ((q t).val k).re)
    (perm : Equiv.Perm (Fin n)) (u t : I)
    (hp : (p t).val ∈ realChamber perm) (hq : (q t).val ∈ realChamber perm) :
    (H (u, t)).val ∈ realChamber perm := by
  intro i j hij
  change ((H (u, t)).val (perm i)).re < ((H (u, t)).val (perm j)).re
  rw [hreal, hreal]
  have hp' := hp hij
  have hq' := hq hij
  by_cases hu : (u : ℝ) = 1
  · simpa only [hu, sub_self, zero_mul, one_mul, zero_add] using hq'
  have hul : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 hu
  have hpos := mul_pos (sub_pos.mpr hul) (sub_pos.mpr hp')
  have hnonneg := mul_nonneg u.property.1 (sub_pos.mpr hq').le
  nlinarith

end BraidNormalForm
end

/- TraceSquareTransport -/
section
set_option autoImplicit false

namespace BraidNormalForm

theorem basedTrace_transport {X : Type*} [TopologicalSpace X]
    {base a b c d : X} (ca : Path base a) (cb : Path base b)
    (cc : Path base c) (cd : Path base d)
    (p : Path a b) (q : Path c d) (left : Path a c) (right : Path b d)
    (hsquare : p.Homotopic (left.trans (q.trans right.symm)))
    (hleft : (ca.trans left).Homotopic cc)
    (hright : (cb.trans right).Homotopic cd) :
    (basedTrace ca p cb).Homotopic (basedTrace cc q cd) := by
  have h₁ := (Path.Homotopic.refl ca).hcomp
    (hsquare.hcomp (Path.Homotopic.refl cb.symm))
  have h₂ : (basedTrace ca (left.trans (q.trans right.symm)) cb).Homotopic
      (basedTrace (ca.trans left) q (cb.trans right)) := by
    apply Path.Homotopic.Quotient.eq.mp
    simp only [basedTrace, Path.trans_symm, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc]
  have h₃ := hleft.hcomp ((Path.Homotopic.refl q).hcomp hright.symm₂)
  exact h₁.trans (h₂.trans h₃)

end BraidNormalForm
end

/- LinearSquareTrace -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG

namespace BraidNormalForm

theorem linear_square_trace_transport {n : ℕ} {a b c d : OrderedConfig n}
    (p : Path a b) (q : Path c d)
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (hreal : ∀ (u t : I) (k : Fin n), ((H (u, t)).val k).re =
      (1 - (u : ℝ)) * ((p t).val k).re + (u : ℝ) * ((q t).val k).re)
    (before after : Equiv.Perm (Fin n))
    (ha : a.val ∈ realChamber before) (hc : c.val ∈ realChamber before)
    (hb : b.val ∈ realChamber after) (hd : d.val ∈ realChamber after) :
    (basedTrace (unorderedChamberApproach before a ha) (p.map (configProj n).continuous)
      (unorderedChamberApproach after b hb)).Homotopic
    (basedTrace (unorderedChamberApproach before c hc) (q.map (configProj n).continuous)
      (unorderedChamberApproach after d hd)) := by
  let left := squareLeft p q H
  let right := squareRight p q H
  have hleft : ∀ u : I, (left u).val ∈ realChamber before := by
    intro u
    exact linear_square_mem_chamber p q H hreal before u 0
      (by simpa only [p.source] using ha) (by simpa only [q.source] using hc)
  have hright : ∀ u : I, (right u).val ∈ realChamber after := by
    intro u
    exact linear_square_mem_chamber p q H hreal after u 1
      (by simpa only [p.target] using hb) (by simpa only [q.target] using hd)
  have hs := (path_square_boundary p q H).map (configProj n)
  have h₁ := Path.map_trans left (q.trans right.symm) (configProj n).continuous
  have h₂ := Path.map_trans q right.symm (configProj n).continuous
  have he := h₁.trans (congrArg (fun γ => (left.map (configProj n).continuous).trans γ) h₂)
  have hs' : (p.map (configProj n).continuous).Homotopic
      ((left.map (configProj n).continuous).trans
        ((q.map (configProj n).continuous).trans (right.map (configProj n).continuous).symm)) := by
    exact Eq.mp (congrArg (fun γ => (p.map (configProj n).continuous).Homotopic γ) he) hs
  exact basedTrace_transport _ _ _ _ _ _ _ _ hs'
    (unorderedChamberApproach_trans_homotopic before left ha hc hleft)
    (unorderedChamberApproach_trans_homotopic after right hb hd hright)

theorem basedTrace_constant_connectors {X : Type*} [TopologicalSpace X]
    {base c d : X} (q : Path c d) (cc : Path base c) (cd : Path base d)
    (hc : c = base) (hd : d = base)
    (hcc : ∀ t, cc t = base) (hcd : ∀ t, cd t = base) :
    (basedTrace cc q cd).Homotopic (q.cast hc.symm hd.symm) := by
  cases hc
  cases hd
  have hec : cc = Path.refl base := by
    apply Path.ext
    funext t
    exact hcc t
  have hed : cd = Path.refl base := by
    apply Path.ext
    funext t
    exact hcd t
  subst cc
  subst cd
  have hrefl : (Path.refl base).symm = Path.refl base := rfl
  apply Path.Homotopic.Quotient.eq.mp
  simp only [basedTrace, hrefl, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

end BraidNormalForm
end

/- ReferenceChambers -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

theorem baseOrdered_mem_identity_chamber (n : ℕ) :
    (baseOrdered n).val ∈ realChamber (Equiv.refl (Fin n)) := by
  intro k l hkl
  change (((k.val : ℂ) + 1).re) < (((l.val : ℂ) + 1).re)
  simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, add_lt_add_iff_right]
  exact_mod_cast hkl

theorem relabelledBase_swap (n : ℕ) (i : Fin (n - 1)) :
    relabelledBase (adjacentSwap i) = referenceEnd n i := by
  calc
    relabelledBase (adjacentSwap i) = relabelConfig (adjacentSwap i) (baseOrdered n) := rfl
    _ = referenceEnd n i := relabel_base_referenceEnd n i

theorem referenceEnd_mem_swap_chamber (n : ℕ) (i : Fin (n - 1)) :
    (referenceEnd n i).val ∈ realChamber (adjacentSwap i) := by
  rw [← relabelledBase_swap n i]
  exact relabelledBase_in_chamber (adjacentSwap i)

theorem identity_approach_base_constant (n : ℕ) (t : I) :
    unorderedChamberApproach (Equiv.refl (Fin n)) (baseOrdered n)
      (baseOrdered_mem_identity_chamber n) t = baseUnordered n := by
  change configProj n (chamberApproach (Equiv.refl (Fin n)) (baseOrdered n)
    (baseOrdered_mem_identity_chamber n) t) = baseUnordered n
  have he : chamberApproach (Equiv.refl (Fin n)) (baseOrdered n)
      (baseOrdered_mem_identity_chamber n) t = baseOrdered n := by
    apply Subtype.ext
    change AffineMap.lineMap (baseOrdered n).val (baseOrdered n).val (t : ℝ) = _
    simp only [AffineMap.lineMap_same, AffineMap.const_apply]
  rw [he]
  rfl

theorem swap_approach_end_constant (n : ℕ) (i : Fin (n - 1)) (t : I) :
    unorderedChamberApproach (adjacentSwap i) (referenceEnd n i)
      (referenceEnd_mem_swap_chamber n i) t = baseUnordered n := by
  change configProj n (chamberApproach (adjacentSwap i) (referenceEnd n i)
    (referenceEnd_mem_swap_chamber n i) t) = baseUnordered n
  have he : chamberApproach (adjacentSwap i) (referenceEnd n i)
      (referenceEnd_mem_swap_chamber n i) t = referenceEnd n i := by
    apply Subtype.ext
    change AffineMap.lineMap (relabelledBase (adjacentSwap i)).val
      (referenceEnd n i).val (t : ℝ) = _
    rw [relabelledBase_swap, AffineMap.lineMap_same, AffineMap.const_apply]
  rw [he]
  exact referenceEnd_projection n i

end BraidNormalForm
end

/- CanonicalCrossingTrace -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

theorem reference_square_trace {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (i : Fin (n - 1))
    (q : Path (baseOrdered n) (referenceEnd n i))
    (H : ContinuousMap.Homotopy p.toContinuousMap q.toContinuousMap)
    (hlinear : LinearSquare p q H)
    (ha : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hb : b.val ∈ realChamber (adjacentSwap i)) :
    (basedTrace (unorderedChamberApproach (Equiv.refl (Fin n)) a ha)
      (p.map (configProj n).continuous)
      (unorderedChamberApproach (adjacentSwap i) b hb)).Homotopic
    ((q.map (configProj n).continuous).cast rfl (referenceEnd_projection n i).symm) := by
  have h := linear_square_trace_transport p q H hlinear.1
    (Equiv.refl (Fin n)) (adjacentSwap i) ha (baseOrdered_mem_identity_chamber n)
    hb (referenceEnd_mem_swap_chamber n i)
  exact h.trans (basedTrace_constant_connectors (q.map (configProj n).continuous)
    (unorderedChamberApproach (Equiv.refl (Fin n)) (baseOrdered n)
      (baseOrdered_mem_identity_chamber n))
    (unorderedChamberApproach (adjacentSwap i) (referenceEnd n i)
      (referenceEnd_mem_swap_chamber n i)) rfl (referenceEnd_projection n i)
    (identity_approach_base_constant n) (swap_approach_end_constant n i))

theorem positive_crossing_trace {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (i : Fin (n - 1))
    (ha : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hb : b.val ∈ realChamber (adjacentSwap i))
    (hpOrder : ∀ (t : I) (k l : Fin n), k < l →
      (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      ((p t).val k).re < ((p t).val l).re)
    (hpImag : ∀ t : I, 0 < ((p t).val (strandIdxSucc i)).im -
      ((p t).val (strandIdx i)).im) :
    (basedTrace (unorderedChamberApproach (Equiv.refl (Fin n)) a ha)
      (p.map (configProj n).continuous)
      (unorderedChamberApproach (adjacentSwap i) b hb)).Homotopic (halfTwistLoop n i) := by
  have hi : strandIdx i < strandIdxSucc i := Nat.lt_succ_self i.val
  have hs : (a.val (strandIdx i)).re < (a.val (strandIdxSucc i)).re := ha hi
  have he : (b.val (strandIdxSucc i)).re < (b.val (strandIdx i)).re := by
    simpa only [adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right] using hb hi
  obtain ⟨H, hH⟩ := positive_crossing_square p i hpOrder hpImag hs he
  have h := reference_square_trace p i (positiveReference n i) H hH ha hb
  exact Eq.mp (congrArg (fun γ =>
    (basedTrace (unorderedChamberApproach (Equiv.refl (Fin n)) a ha)
      (p.map (configProj n).continuous)
      (unorderedChamberApproach (adjacentSwap i) b hb)).Homotopic γ)
    (positiveReference_projection n i)) h

theorem negative_crossing_trace {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (i : Fin (n - 1))
    (ha : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hb : b.val ∈ realChamber (adjacentSwap i))
    (hpOrder : ∀ (t : I) (k l : Fin n), k < l →
      (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      ((p t).val k).re < ((p t).val l).re)
    (hpImag : ∀ t : I, ((p t).val (strandIdxSucc i)).im -
      ((p t).val (strandIdx i)).im < 0) :
    (basedTrace (unorderedChamberApproach (Equiv.refl (Fin n)) a ha)
      (p.map (configProj n).continuous)
      (unorderedChamberApproach (adjacentSwap i) b hb)).Homotopic (halfTwistLoop n i).symm := by
  have hi : strandIdx i < strandIdxSucc i := Nat.lt_succ_self i.val
  have hs : (a.val (strandIdx i)).re < (a.val (strandIdxSucc i)).re := ha hi
  have he : (b.val (strandIdxSucc i)).re < (b.val (strandIdx i)).re := by
    simpa only [adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right] using hb hi
  obtain ⟨H, hH⟩ := negative_crossing_square p i hpOrder hpImag hs he
  have h := reference_square_trace p i (negativeReference n i) H hH ha hb
  exact Eq.mp (congrArg (fun γ =>
    (basedTrace (unorderedChamberApproach (Equiv.refl (Fin n)) a ha)
      (p.map (configProj n).continuous)
      (unorderedChamberApproach (adjacentSwap i) b hb)).Homotopic γ)
    (negativeReference_projection n i)) h

end BraidNormalForm
end

/- CanonicalConnectorChoice -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

theorem realChamber_real_injective {n : ℕ} {perm : Equiv.Perm (Fin n)}
    {z : OrderedConfig n} (hz : z.val ∈ realChamber perm) :
    Function.Injective (fun i => (z.val i).re) := by
  intro i j hij
  obtain ⟨i', rfl⟩ := perm.surjective i
  obtain ⟨j', rfl⟩ := perm.surjective j
  exact congrArg perm (hz.injective hij)

theorem canonicalChamberApproach_eq_of_mem {n : ℕ} (perm : Equiv.Perm (Fin n))
    (z : OrderedConfig n) (hz : Function.Injective (fun i => (z.val i).re))
    (hmem : z.val ∈ realChamber perm) :
    canonicalChamberApproach z hz = unorderedChamberApproach perm z hmem := by
  have hs := sorting_permutation_unique (fun i => (z.val i).re)
    (sortingPermutation_strictMono z hz) hmem
  apply Path.ext
  funext t
  apply congrArg (configProj n)
  apply Subtype.ext
  change AffineMap.lineMap (relabelledBase (sortingPermutation z hz)).val z.val (t : ℝ) =
    AffineMap.lineMap (relabelledBase perm).val z.val (t : ℝ)
  rw [hs]

theorem no_crossing_canonical_trace_null {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hreal : ∀ t : I, Function.Injective (fun i => ((p t).val i).re)) :
    (basedTrace (canonicalChamberApproach a ha) (p.map (configProj n).continuous)
      (canonicalChamberApproach b hb)).Homotopic (Path.refl (baseUnordered n)) := by
  let perm := sortingPermutation a ha
  have ham : a.val ∈ realChamber perm := sortingPermutation_strictMono a ha
  have hp := no_crossing_path_in_chamber perm p ham hreal
  have hbm : b.val ∈ realChamber perm := by simpa only [p.target] using hp 1
  rw [canonicalChamberApproach_eq_of_mem perm a ha ham,
    canonicalChamberApproach_eq_of_mem perm b hb hbm]
  exact unordered_chamber_trace_null perm p ham hbm hp

theorem positive_canonical_crossing_trace {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (i : Fin (n - 1))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (ham : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hbm : b.val ∈ realChamber (adjacentSwap i))
    (hpOrder : ∀ (t : I) (k l : Fin n), k < l →
      (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      ((p t).val k).re < ((p t).val l).re)
    (hpImag : ∀ t : I, 0 < ((p t).val (strandIdxSucc i)).im -
      ((p t).val (strandIdx i)).im) :
    (basedTrace (canonicalChamberApproach a ha) (p.map (configProj n).continuous)
      (canonicalChamberApproach b hb)).Homotopic (halfTwistLoop n i) := by
  rw [canonicalChamberApproach_eq_of_mem _ a ha ham,
    canonicalChamberApproach_eq_of_mem _ b hb hbm]
  exact positive_crossing_trace p i ham hbm hpOrder hpImag

theorem negative_canonical_crossing_trace {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (i : Fin (n - 1))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (ham : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hbm : b.val ∈ realChamber (adjacentSwap i))
    (hpOrder : ∀ (t : I) (k l : Fin n), k < l →
      (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      ((p t).val k).re < ((p t).val l).re)
    (hpImag : ∀ t : I, ((p t).val (strandIdxSucc i)).im -
      ((p t).val (strandIdx i)).im < 0) :
    (basedTrace (canonicalChamberApproach a ha) (p.map (configProj n).continuous)
      (canonicalChamberApproach b hb)).Homotopic (halfTwistLoop n i).symm := by
  rw [canonicalChamberApproach_eq_of_mem _ a ha ham,
    canonicalChamberApproach_eq_of_mem _ b hb hbm]
  exact negative_crossing_trace p i ham hbm hpOrder hpImag

end BraidNormalForm
end

/- LocalNormalFormInterface -/
section
set_option autoImplicit false

open Set unitInterval
open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

def TraceHasWord {n : ℕ} {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re)) : Prop :=
  ∃ w : List (BraidLetter n),
    (basedTrace (canonicalChamberApproach a ha) (p.map (configProj n).continuous)
      (canonicalChamberApproach b hb)).Homotopic (braidWordLoop n w)

def LocalAffineWordProperty (n : ℕ) : Prop :=
  ∀ {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re)),
    (∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ)) →
    GoodChart p univ → TraceHasWord p ha hb

end BraidNormalForm
end

/- TraceWordCalculus -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

theorem map_concat {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {m : ℕ} (v : Fin (m + 1) → X)
    (p : (k : Fin m) → Path (v k.castSucc) (v k.succ)) :
    (Path.concat v p).map f.continuous =
      Path.concat (fun k => f (v k)) (fun k => (p k).map f.continuous) := by
  induction m with
  | zero =>
    rw [Path.concat_zero, Path.concat_zero]
    apply Path.ext
    funext t
    rfl
  | succ m ih =>
    have h₁ := congrArg (fun γ : Path (v 0) (v (Fin.last (m + 1))) => γ.map f.continuous)
      (Path.concat_succ v p)
    have h₂ := Path.map_trans (Path.concat (v ∘ Fin.castSucc) (fun k => p k.castSucc))
      (p (Fin.last m)) f.continuous
    have h₃ := congrArg (fun γ => γ.trans ((p (Fin.last m)).map f.continuous))
      (ih (v ∘ Fin.castSucc) (fun k => p k.castSucc))
    have h₄ := Path.concat_succ (fun k => f (v k)) (fun k => (p k).map f.continuous)
    exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

theorem trace_word_homotopy {n : ℕ} {a b : OrderedConfig n}
    {p q : Path a b}
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (h : p.Homotopic q) (hq : TraceHasWord q ha hb) : TraceHasWord p ha hb := by
  obtain ⟨w, hw⟩ := hq
  exact ⟨w, ((Path.Homotopic.refl (canonicalChamberApproach a ha)).hcomp
    ((h.map (configProj n)).hcomp
      (Path.Homotopic.refl (canonicalChamberApproach b hb).symm))).trans hw⟩

theorem trace_word_cast {n : ℕ} {a b a' b' : OrderedConfig n}
    (p : Path a b) (h0 : a' = a) (h1 : b' = b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (ha' : Function.Injective (fun i => (a'.val i).re))
    (hb' : Function.Injective (fun i => (b'.val i).re))
    (hp : TraceHasWord p ha hb) : TraceHasWord (p.cast h0 h1) ha' hb' := by
  cases h0
  cases h1
  have he : p.cast rfl rfl = p := by
    apply Path.ext
    funext t
    rfl
  rw [he]
  exact hp

theorem trace_word_trans {n : ℕ} {a b c : OrderedConfig n}
    (p : Path a b) (q : Path b c)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hc : Function.Injective (fun i => (c.val i).re))
    (hp : TraceHasWord p ha hb) (hq : TraceHasWord q hb hc) :
    TraceHasWord (p.trans q) ha hc := by
  obtain ⟨u, hu⟩ := hp
  obtain ⟨v, hv⟩ := hq
  have happ : (braidWordLoop n (v ++ u)).Homotopic
      ((braidWordLoop n u).trans (braidWordLoop n v)) := by
    simpa only [TarchaBraids.NormalForm.wordLoop_eq_braidWordLoop] using
      wordLoop_append (braidLetterLoop n) v u
  have ht := (basedTrace_trans (canonicalChamberApproach a ha)
    (canonicalChamberApproach b hb) (canonicalChamberApproach c hc)
    (p.map (configProj n).continuous) (q.map (configProj n).continuous)).trans
      ((hu.hcomp hv).trans happ.symm)
  have he := congrArg (fun γ => basedTrace (canonicalChamberApproach a ha) γ
    (canonicalChamberApproach c hc)) (Path.map_trans p q (configProj n).continuous)
  exact ⟨v ++ u, Eq.mp (congrArg (fun γ => γ.Homotopic (braidWordLoop n (v ++ u))) he.symm) ht⟩

theorem trace_word_concat {n m : ℕ} (v : Fin (m + 1) → OrderedConfig n)
    (p : (k : Fin m) → Path (v k.castSucc) (v k.succ))
    (hv : ∀ k, Function.Injective (fun i => ((v k).val i).re))
    (hp : ∀ k, TraceHasWord (p k) (hv k.castSucc) (hv k.succ)) :
    TraceHasWord (Path.concat v p) (hv 0) (hv (Fin.last m)) := by
  have h := TarchaBraids.NormalForm.concat_has_braid_word n
    (fun k => configProj n (v k)) (fun k => (p k).map (configProj n).continuous)
    (fun k => canonicalChamberApproach (v k) (hv k)) hp
  obtain ⟨w, hw⟩ := h
  have he := congrArg (fun γ => basedTrace (canonicalChamberApproach (v 0) (hv 0)) γ
    (canonicalChamberApproach (v (Fin.last m)) (hv (Fin.last m)))) (map_concat (configProj n) v p)
  exact ⟨w, Eq.mp (congrArg (fun γ => γ.Homotopic (braidWordLoop n w)) he.symm) hw⟩

end BraidNormalForm
end

/- GenericWaypoint -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set

noncomputable section

namespace BraidNormalForm

private def DistinctPairPair (n : ℕ) :=
  {pq : StrandPair n × StrandPair n // pq.1 ≠ pq.2}

private instance (n : ℕ) : Fintype (DistinctPairPair n) :=
  inferInstanceAs (Fintype {pq : StrandPair n × StrandPair n // pq.1 ≠ pq.2})

private def waypointConstraint {n : ℕ} (a b : Fin n → ℂ) :
    StrandPair n ⊕ (Bool × DistinctPairPair n) → (Fin n → ℂ) →L[ℝ] ℝ
  | Sum.inl p => realGap p
  | Sum.inr (side, pq) => crossingDet (if side then b else a) pq.val.1 pq.val.2

/-- A waypoint in any nonempty open cell makes both new affine segments have
real-distinct vertices and no simultaneous pair crossings. The original path
is not required to be generic. -/
theorem exists_generic_waypoint {n : ℕ} (a b : Fin n → ℂ)
    (ha : Function.Injective (fun j => (a j).re))
    (hb : Function.Injective (fun j => (b j).re))
    {C : Set (Fin n → ℂ)} (hC : IsOpen C) (hne : C.Nonempty) :
    ∃ c ∈ C,
      Function.Injective (fun j => (c j).re) ∧
      (∀ p q : StrandPair n, p ≠ q → crossingDet a p q c ≠ 0) ∧
      (∀ p q : StrandPair n, p ≠ q → crossingDet c p q b ≠ 0) := by
  have hproper : ∀ i, waypointConstraint a b i ≠ 0 := by
    intro i
    rcases i with p | ⟨side, pq⟩
    · exact realGap_ne_zero p
    · cases side
      · exact crossingDet_ne_zero ha pq.property
      · exact crossingDet_ne_zero hb pq.property
  obtain ⟨c, hc, hav⟩ := exists_mem_open_avoiding_linear
    (waypointConstraint a b) hproper hC hne
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · intro i j he
    by_contra hneij
    rcases lt_or_gt_of_ne hneij with hij | hji
    · have h := hav (Sum.inl ⟨(i, j), hij⟩)
      apply h
      change (c i).re - (c j).re = 0
      exact sub_eq_zero.mpr he
    · have h := hav (Sum.inl ⟨(j, i), hji⟩)
      apply h
      change (c j).re - (c i).re = 0
      exact sub_eq_zero.mpr he.symm
  · intro p q hpq
    exact hav (Sum.inr (false, ⟨(p, q), hpq⟩))
  · intro p q hpq hzero
    have h := hav (Sum.inr (true, ⟨(p, q), hpq⟩))
    apply h
    change crossingDet b p q c = 0
    rw [crossingDet_apply] at hzero ⊢
    nlinarith [hzero]

/-- The two halves selected by the waypoint theorem each have at most one
unordered pair at any crossing time, and every crossing has nonzero slope. -/
theorem exists_simple_crossing_waypoint {n : ℕ} (a b : Fin n → ℂ)
    (ha : Function.Injective (fun j => (a j).re))
    (hb : Function.Injective (fun j => (b j).re))
    {C : Set (Fin n → ℂ)} (hC : IsOpen C) (hne : C.Nonempty) :
    ∃ c ∈ C, Function.Injective (fun j => (c j).re) ∧
      (∀ (t : ℝ) (p q : StrandPair n), realGap p (AffineMap.lineMap a c t) = 0 →
        realGap q (AffineMap.lineMap a c t) = 0 → p = q) ∧
      (∀ (t : ℝ) (p q : StrandPair n), realGap p (AffineMap.lineMap c b t) = 0 →
        realGap q (AffineMap.lineMap c b t) = 0 → p = q) ∧
      (∀ (t : ℝ) (p : StrandPair n), realGap p (AffineMap.lineMap a c t) = 0 →
        realGap p c - realGap p a ≠ 0) ∧
      (∀ (t : ℝ) (p : StrandPair n), realGap p (AffineMap.lineMap c b t) = 0 →
        realGap p b - realGap p c ≠ 0) := by
  obtain ⟨c, hc, hci, hac, hcb⟩ := exists_generic_waypoint a b ha hb hC hne
  exact ⟨c, hc, hci,
    fun t _ _ hp hq => lineMap_crossing_unique ha hac t hp hq,
    fun t _ _ hp hq => lineMap_crossing_unique hci hcb t hp hq,
    fun t p hp => lineMap_crossing_slope_ne_zero ha p t hp,
    fun t p hp => lineMap_crossing_slope_ne_zero hci p t hp⟩

end BraidNormalForm

end
end

/- ConvexGenericRefinement -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set unitInterval
open scoped Convex

noncomputable section
namespace BraidNormalForm

/-- Replace a path inside one open convex collision-free cell by two affine
segments. Simultaneous crossings and tangencies are excluded by the proved
waypoint constraints, while the homotopy stays in that same safe cell. -/
theorem convex_generic_refinement {n : ℕ} {a b : configurations n}
    (p : Path a b)
    (ha : Function.Injective (fun j => (a.val j).re))
    (hb : Function.Injective (fun j => (b.val j).re))
    {C : Set (Fin n → ℂ)} (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hCU : C ⊆ configurations n) (hp : ∀ t : I, (p t).val ∈ C) :
    ∃ (c : configurations n) (q : Path a c) (r : Path c b),
      c.val ∈ C ∧ Function.Injective (fun j => (c.val j).re) ∧
      (∀ t, (q t).val = AffineMap.lineMap a.val c.val (t : ℝ)) ∧
      (∀ t, (r t).val = AffineMap.lineMap c.val b.val (t : ℝ)) ∧
      (∀ t p₁ p₂, realGap p₁ (q t).val = 0 → realGap p₂ (q t).val = 0 → p₁ = p₂) ∧
      (∀ t p₁ p₂, realGap p₁ (r t).val = 0 → realGap p₂ (r t).val = 0 → p₁ = p₂) ∧
      (∀ t p₁, realGap p₁ (q t).val = 0 → realGap p₁ c.val - realGap p₁ a.val ≠ 0) ∧
      (∀ t p₁, realGap p₁ (r t).val = 0 → realGap p₁ b.val - realGap p₁ c.val ≠ 0) ∧
      p.Homotopic (q.trans r) := by
  have haC : a.val ∈ C := by simpa only [p.source] using hp 0
  have hbC : b.val ∈ C := by simpa only [p.target] using hp 1
  obtain ⟨c, hc, hci, huniq1, huniq2, hslope1, hslope2⟩ :=
    exists_simple_crossing_waypoint a.val b.val ha hb hCo ⟨a.val, haC⟩
  let c' : configurations n := ⟨c, hCU hc⟩
  let hac : segment ℝ a.val c ⊆ configurations n :=
    (hCc.segment_subset haC hc).trans hCU
  let hcb : segment ℝ c b.val ⊆ configurations n :=
    (hCc.segment_subset hc hbC).trans hCU
  let q : Path a c' := segmentIn a c' hac
  let r : Path c' b := segmentIn c' b hcb
  refine ⟨c', q, r, hc, hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t; rfl
  · intro t; rfl
  · intro t p₁ p₂ h₁ h₂
    exact huniq1 (t : ℝ) p₁ p₂ h₁ h₂
  · intro t p₁ p₂ h₁ h₂
    exact huniq2 (t : ℝ) p₁ p₂ h₁ h₂
  · intro t p₁ h₁
    exact hslope1 (t : ℝ) p₁ h₁
  · intro t p₁ h₁
    exact hslope2 (t : ℝ) p₁ h₁
  · apply convex_paths_homotopic hCc hCU p (q.trans r) hp
    let S : Set (configurations n) := {z | z.val ∈ C}
    have hq : Set.range q ⊆ S := by
      rintro _ ⟨t, rfl⟩
      exact segmentIn_mem hCc haC hc hac t
    have hr : Set.range r ⊆ S := by
      rintro _ ⟨t, rfl⟩
      exact segmentIn_mem hCc hc hbC hcb t
    have hqr : Set.range (q.trans r) ⊆ S := by
      rw [Path.trans_range]
      exact Set.union_subset hq hr
    intro t
    exact hqr ⟨t, rfl⟩

end BraidNormalForm
end
end

/- AffineSafeCell -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set unitInterval Metric
open scoped Convex

namespace BraidNormalForm

/-- A collision-free affine configuration path has an open convex
collision-free neighborhood. This recovers a safe cell from the checked
polygonal interface without imposing any additional hypothesis. -/
theorem affine_configuration_safe_cell {n : ℕ} {a b : configurations n}
    (p : Path a b)
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ)) :
    ∃ C : Set (Fin n → ℂ), IsOpen C ∧ Convex ℝ C ∧
      C ⊆ configurations n ∧ ∀ t : I, (p t).val ∈ C := by
  have hcompact : IsCompact (segment ℝ a.val b.val) := by
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment a.val b.val).continuous
  have hsub : segment ℝ a.val b.val ⊆ configurations n := by
    intro x hx
    rw [← Path.range_segment] at hx
    obtain ⟨t, rfl⟩ := hx
    change AffineMap.lineMap a.val b.val (t : ℝ) ∈ configurations n
    rw [← hp t]
    exact (p t).property
  obtain ⟨δ, hδ, hδsub⟩ :=
    hcompact.exists_thickening_subset_open (configurations_open n) hsub
  refine ⟨thickening δ (segment ℝ a.val b.val), isOpen_thickening,
    (convex_segment (𝕜 := ℝ) a.val b.val).thickening δ, hδsub, ?_⟩
  intro t
  apply self_subset_thickening hδ
  rw [hp t, ← Path.range_segment]
  exact ⟨t, rfl⟩

end BraidNormalForm
end

/- AffineSimpleRefinement -/
section
set_option autoImplicit false

open Set unitInterval

namespace BraidNormalForm

/-- Every affine collision-free path with real-distinct endpoints admits a
collision-free, endpoint-preserving refinement into two affine paths with
simple transverse crossings. No generic-position hypothesis is added. -/
theorem affine_path_has_simple_refinement {n : ℕ} {a b : configurations n}
    (p : Path a b)
    (ha : Function.Injective (fun j => (a.val j).re))
    (hb : Function.Injective (fun j => (b.val j).re))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ)) :
    ∃ (c : configurations n) (q : Path a c) (r : Path c b),
      Function.Injective (fun j => (c.val j).re) ∧
      (∀ t, (q t).val = AffineMap.lineMap a.val c.val (t : ℝ)) ∧
      (∀ t, (r t).val = AffineMap.lineMap c.val b.val (t : ℝ)) ∧
      (∀ t p₁ p₂, realGap p₁ (q t).val = 0 → realGap p₂ (q t).val = 0 → p₁ = p₂) ∧
      (∀ t p₁ p₂, realGap p₁ (r t).val = 0 → realGap p₂ (r t).val = 0 → p₁ = p₂) ∧
      (∀ t p₁, realGap p₁ (q t).val = 0 → realGap p₁ c.val - realGap p₁ a.val ≠ 0) ∧
      (∀ t p₁, realGap p₁ (r t).val = 0 → realGap p₁ b.val - realGap p₁ c.val ≠ 0) ∧
      p.Homotopic (q.trans r) := by
  obtain ⟨C, hCo, hCc, hCU, hpC⟩ := affine_configuration_safe_cell p hp
  obtain ⟨c, q, r, _, hci, hq, hr, hqu, hru, hqs, hrs, hhom⟩ :=
    convex_generic_refinement p ha hb hCo hCc hCU hpC
  exact ⟨c, q, r, hci, hq, hr, hqu, hru, hqs, hrs, hhom⟩

end BraidNormalForm
end

/- RealVertexPerturbation -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set unitInterval

namespace BraidNormalForm

def perturb {n : ℕ} (ε : ℝ) (f : I → Fin n → ℂ) (t : I) (j : Fin n) : ℂ :=
  f t j + ((ε * (t : ℝ) * (1 - (t : ℝ)) * (j.val : ℝ) : ℝ) : ℂ)

@[simp] lemma perturb_zero {n : ℕ} (ε : ℝ) (f : I → Fin n → ℂ) :
    perturb ε f 0 = f 0 := by funext j; simp [perturb]

@[simp] lemma perturb_one {n : ℕ} (ε : ℝ) (f : I → Fin n → ℂ) :
    perturb ε f 1 = f 1 := by funext j; simp [perturb]

lemma perturb_continuous {n : ℕ} (ε : ℝ) (f : I → Fin n → ℂ) (hf : Continuous f) :
    Continuous (perturb ε f) := by
  apply continuous_pi
  intro j
  unfold perturb
  fun_prop

lemma perturb_dist_le {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) (f : I → Fin n → ℂ) (t : I) :
    dist (perturb ε f t) (f t) ≤ ε * (n : ℝ) := by
  apply (dist_pi_le_iff (mul_nonneg hε (Nat.cast_nonneg n))).mpr
  intro j
  have ht : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have htime : (t : ℝ) * (1 - (t : ℝ)) ≤ 1 := by nlinarith [t.property.2, sq_nonneg (t : ℝ)]
  have hj : (0 : ℝ) ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hjn : (j.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast j.isLt.le
  have hx : 0 ≤ ε * (t : ℝ) * (1 - (t : ℝ)) * (j.val : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg hε t.property.1) ht) hj
  simp only [perturb, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg hx]
  calc
    ε * (t : ℝ) * (1 - (t : ℝ)) * (j.val : ℝ) =
        ε * ((t : ℝ) * (1 - (t : ℝ)) * (j.val : ℝ)) := by ring
    _ ≤ ε * (j.val : ℝ) := mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right htime hj) hε
    _ ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_left hjn hε

theorem exists_real_distinct_vertices {n m : ℕ} (f : I → Fin n → ℂ)
    (h0 : Function.Injective (fun j => (f 0 j).re))
    (h1 : Function.Injective (fun j => (f 1 j).re))
    (t : Fin (m + 1) → I) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, ε ∈ Ioo 0 η ∧
      ∀ k, Function.Injective (fun j => (perturb ε f (t k) j).re) := by
  let bad : (Fin (m + 1) × Fin n × Fin n) → ℝ := fun p =>
    ((f (t p.1) p.2.2).re - (f (t p.1) p.2.1).re) /
      ((t p.1 : ℝ) * (1 - (t p.1 : ℝ)) * ((p.2.1.val : ℝ) - (p.2.2.val : ℝ)))
  obtain ⟨ε, hε, havoid⟩ := ((Ioo_infinite hη).sdiff (finite_range bad)).nonempty
  refine ⟨ε, hε, ?_⟩
  intro k
  by_cases ht0 : t k = 0
  · simpa only [ht0, perturb_zero] using h0
  by_cases ht1 : t k = 1
  · simpa only [ht1, perturb_one] using h1
  intro i j hij
  by_contra hne
  have ht0' : (t k : ℝ) ≠ 0 := fun h => ht0 (Subtype.ext h)
  have ht1' : 1 - (t k : ℝ) ≠ 0 := by
    intro h
    apply ht1
    apply Subtype.ext
    change (t k : ℝ) = 1
    linarith
  have hij' : (i.val : ℝ) - (j.val : ℝ) ≠ 0 := by
    intro h
    apply hne
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  have hd : (t k : ℝ) * (1 - (t k : ℝ)) * ((i.val : ℝ) - (j.val : ℝ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ht0' ht1') hij'
  have he : ε = bad (k, i, j) := by
    apply (eq_div_iff hd).mpr
    simp only [perturb, Complex.add_re, Complex.ofReal_re] at hij
    nlinarith
  exact havoid ⟨(k, i, j), he.symm⟩

end BraidNormalForm
end

/- PerturbedPath -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set unitInterval

noncomputable section

namespace BraidNormalForm

variable {n : ℕ} {a b : configurations n}

def perturbPath (p : Path a b) (ε : ℝ)
    (hinj : ∀ t, Function.Injective (perturb ε (fun s => (p s).val) t)) : Path a b where
  toFun t := ⟨perturb ε (fun s => (p s).val) t, hinj t⟩
  continuous_toFun :=
    (perturb_continuous ε (fun s => (p s).val)
      (continuous_subtype_val.comp p.continuous)).subtype_mk _
  source' := by
    apply Subtype.ext
    exact (perturb_zero ε (fun s => (p s).val)).trans (congrArg Subtype.val p.source)
  target' := by
    apply Subtype.ext
    exact (perturb_one ε (fun s => (p s).val)).trans (congrArg Subtype.val p.target)

theorem exists_homotopic_perturbation (p : Path a b) {ε r : ℝ} (hε : 0 ≤ ε)
    (hclear : ∀ (t : I) (q : Fin n → ℂ), dist q (p t).val < r → Function.Injective q)
    (hbound : ε * (n : ℝ) < r) :
    ∃ q : Path a b, (∀ t, (q t).val = perturb ε (fun s => (p s).val) t) ∧ p.Homotopic q := by
  let f : I → Fin n → ℂ := fun s => (p s).val
  have hf : Continuous f := continuous_subtype_val.comp p.continuous
  have hAll (u t : I) : Function.Injective (perturb ((u : ℝ) * ε) f t) := by
    apply hclear t
    refine (perturb_dist_le (mul_nonneg u.property.1 hε) f t).trans_lt ?_
    have hu : (u : ℝ) * ε ≤ ε := by nlinarith [u.property.2]
    exact (mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg n)).trans_lt hbound
  have htop : ∀ t, Function.Injective (perturb ε f t) := by
    intro t
    simpa only [Set.Icc.coe_one, one_mul] using hAll 1 t
  let q := perturbPath p ε htop
  refine ⟨q, fun _ => rfl, ?_⟩
  refine ⟨{
    toFun := fun x => ⟨perturb ((x.1 : ℝ) * ε) f x.2, hAll x.1 x.2⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_
  }⟩
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    unfold perturb
    fun_prop
  · intro t
    apply Subtype.ext
    funext j
    simp [perturb, f]
  · intro t
    apply Subtype.ext
    funext j
    simp [q, perturbPath, perturb, f]
  · intro u t ht
    rcases ht with (rfl | rfl)
    · apply Subtype.ext
      exact perturb_zero ((u : ℝ) * ε) f
    · apply Subtype.ext
      exact perturb_one ((u : ℝ) * ε) f

end BraidNormalForm

end
end

/- FiniteBallSubdivision -/
section
set_option autoImplicit false

open Set unitInterval Metric

namespace BraidNormalForm

theorem finite_ball_subdivision {E : Type*} [PseudoMetricSpace E]
    (f : I → E) (hf : Continuous f) {r : ℝ} (hr : 0 < r) :
    ∃ (m : ℕ) (t : Fin (m + 1) → I) (c : Fin m → I),
      t 0 = 0 ∧ t (Fin.last m) = 1 ∧ Monotone t ∧
      ∀ (k : Fin m) (s : I), s ∈ Icc (t k.castSucc) (t k.succ) →
        dist (f s) (f (c k)) < r := by
  let C : I → Set I := fun u => f ⁻¹' ball (f u) r
  have ho : ∀ u, IsOpen (C u) := fun u => isOpen_ball.preimage hf
  have hu : univ ⊆ ⋃ u, C u := by
    intro s _
    apply mem_iUnion.mpr
    refine ⟨s, ?_⟩
    change dist (f s) (f s) < r
    simpa only [dist_self] using hr
  obtain ⟨τ, hτ0, hτmono, ⟨m, hm⟩, hτ⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval ho hu
  let t : Fin (m + 1) → I := fun k => τ k.val
  let c : Fin m → I := fun k => (hτ k.val).choose
  refine ⟨m, t, c, hτ0, hm m le_rfl, ?_, ?_⟩
  · intro i j hij
    exact hτmono hij
  · intro k s hs
    exact (hτ k.val).choose_spec hs

end BraidNormalForm
end

/- PolygonalConfiguration -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval Metric

noncomputable section

namespace BraidNormalForm

theorem exists_polygonal_configuration_path {n : ℕ} {a b : configurations n}
    (p : Path a b)
    (ha : Function.Injective (fun j => (a.val j).re))
    (hb : Function.Injective (fun j => (b.val j).re)) :
    ∃ (m : ℕ) (v : Fin (m + 1) → configurations n)
      (segments : (k : Fin m) → Path (v k.castSucc) (v k.succ)),
      (∀ k, Function.Injective (fun j => ((v k).val j).re)) ∧
      (∀ k s, (segments k s).val =
        AffineMap.lineMap (v k.castSucc).val (v k.succ).val (s : ℝ)) ∧
      ∃ (h0 : a = v 0) (h1 : b = v (Fin.last m)),
        p.Homotopic ((Path.concat v segments).cast h0 h1) := by
  let f : I → Fin n → ℂ := fun t => (p t).val
  have hf : Continuous f := continuous_subtype_val.comp p.continuous
  obtain ⟨δ, hδ, hclear⟩ := uniform_configuration_clearance n f hf (fun t => (p t).property)
  let r : ℝ := δ / 2
  have hr : 0 < r := half_pos hδ
  have hrδ : r < δ := half_lt_self hδ
  obtain ⟨m, t, c, ht0, ht1, htmono, hsub⟩ := finite_ball_subdivision f hf (half_pos hr)
  have hf0 : Function.Injective (fun j => (f 0 j).re) := by
    simpa only [f, p.source] using ha
  have hf1 : Function.Injective (fun j => (f 1 j).re) := by
    simpa only [f, p.target] using hb
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨ε, hε, hreal⟩ := exists_real_distinct_vertices f hf0 hf1 t (div_pos hr hden)
  have hpert : ε * (n : ℝ) < r / 2 := by
    have h := (lt_div_iff₀ hden).mp hε.2
    nlinarith [hε.1]
  obtain ⟨q, hq, hpq⟩ := exists_homotopic_perturbation p hε.1.le hclear
    (hpert.trans ((half_lt_self hr).trans hrδ))
  let C : Fin m → Set (Fin n → ℂ) := fun k => ball (f (c k)) r
  have hC : ∀ k, Convex ℝ (C k) := fun k => convex_ball _ _
  have hCU : ∀ k, C k ⊆ configurations n := by
    intro k z hz
    exact hclear (c k) z (hz.trans hrδ)
  have hqC : ∀ (k : Fin m) (s : I),
      (q.subpath (t k.castSucc) (t k.succ) s).val ∈ C k := by
    intro k s
    have hle : t k.castSucc ≤ t k.succ := htmono (by
      change k.val ≤ k.val + 1
      omega)
    have hm : q.subpath (t k.castSucc) (t k.succ) s ∈
        q '' Icc (t k.castSucc) (t k.succ) := by
      rw [← Path.range_subpath_of_le q _ _ hle]
      exact ⟨s, rfl⟩
    obtain ⟨u, hu, he⟩ := hm
    rw [← he]
    change dist (q u).val (f (c k)) < r
    rw [hq]
    calc
      dist (perturb ε f u) (f (c k)) ≤
          dist (perturb ε f u) (f u) + dist (f u) (f (c k)) := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add
        ((perturb_dist_le hε.1.le f u).trans_lt hpert) (hsub k u hu)
      _ = r := by ring
  obtain ⟨segments, hsegments, hhom⟩ := polygonal_subpath_replacement q t C hC hCU hqC
  let h0 : a = (q ∘ t) 0 := ((congrArg q ht0).trans q.source).symm
  let h1 : b = (q ∘ t) (Fin.last m) := ((congrArg q ht1).trans q.target).symm
  refine ⟨m, q ∘ t, segments, ?_, hsegments, h0, h1, ?_⟩
  · intro k
    change Function.Injective (fun j => ((q (t k)).val j).re)
    rw [hq]
    exact hreal k
  · have hs := hhom.pathCast h0 h1
    have he : (q.subpath (t 0) (t (Fin.last m))).cast h0 h1 = q := by
      apply Path.ext
      funext s
      change q.subpath (t 0) (t (Fin.last m)) s = q s
      rw [ht0, ht1, Path.subpath_zero_one]
      rfl
    have he' := congrArg (fun γ : Path a b =>
      γ.Homotopic ((Path.concat (q ∘ t) segments).cast h0 h1)) he
    exact hpq.trans (Eq.mp he' hs)

end BraidNormalForm

end
end

/- PathCrossingFinite -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open unitInterval

namespace TarchaBraids.NormalForm

def crossingTimes {T X ι : Type*} (coord : X → ι → ℝ) (f : T → X) : Set T :=
  {t | ∃ i j : ι, i ≠ j ∧ coord (f t) i = coord (f t) j}

variable {X ι : Type*} [TopologicalSpace X] (coord : X → ι → ℝ)

theorem crossingTimes_extend_finite {a b : X} (p : Path a b)
    (ha : Function.Injective (coord a)) (hb : Function.Injective (coord b))
    (hp : (crossingTimes coord p).Finite) : (crossingTimes coord p.extend).Finite := by
  apply (hp.image (Subtype.val : I → ℝ)).subset
  rintro t ⟨i, j, hij, he⟩
  by_cases h0 : t ≤ 0
  · rw [Path.extend_of_le_zero p h0] at he
    exact False.elim (hij (ha he))
  by_cases h1 : 1 ≤ t
  · rw [Path.extend_of_one_le p h1] at he
    exact False.elim (hij (hb he))
  let u : I := ⟨t, ⟨le_of_not_ge h0, le_of_not_ge h1⟩⟩
  refine ⟨u, ⟨i, j, hij, ?_⟩, rfl⟩
  simpa only [← Path.extend_extends' p u] using he

theorem crossingTimes_trans_finite {a b c : X} (p : Path a b) (q : Path b c)
    (ha : Function.Injective (coord a)) (hb : Function.Injective (coord b))
    (hc : Function.Injective (coord c))
    (hp : (crossingTimes coord p).Finite) (hq : (crossingTimes coord q).Finite) :
    (crossingTimes coord (p.trans q)).Finite := by
  have hp' := crossingTimes_extend_finite coord p ha hb hp
  have hq' := crossingTimes_extend_finite coord q hb hc hq
  have hl := Set.Finite.preimage (f := fun t : ℝ => 2 * t)
    (fun _ _ _ _ h => by linarith) hp'
  have hr := Set.Finite.preimage (f := fun t : ℝ => 2 * t - 1)
    (fun _ _ _ _ h => by linarith) hq'
  have hext : (crossingTimes coord (p.trans q).extend).Finite := by
    apply (hl.union hr).subset
    rintro t ⟨i, j, hij, he⟩
    by_cases ht : t ≤ 1 / 2
    · apply Or.inl
      exact ⟨i, j, hij, by simpa only [Path.extend_trans_of_le_half p q ht] using he⟩
    · apply Or.inr
      exact ⟨i, j, hij, by
        simpa only [Path.extend_trans_of_half_le p q (le_of_not_ge ht)] using he⟩
  have hpre := Set.Finite.preimage (f := (Subtype.val : I → ℝ))
    (fun _ _ _ _ h => Subtype.ext h) hext
  apply hpre.subset
  rintro t ⟨i, j, hij, he⟩
  exact ⟨i, j, hij, by simpa only [Path.extend_extends'] using he⟩

theorem crossingTimes_refl_finite {a : X} (ha : Function.Injective (coord a)) :
    (crossingTimes coord (Path.refl a)).Finite := by
  apply Set.finite_empty.subset
  rintro t ⟨i, j, hij, he⟩
  exact False.elim (hij (ha he))

theorem crossingTimes_concat_finite {m : ℕ} (v : Fin (m + 1) → X)
    (p : (k : Fin m) → Path (v k.castSucc) (v k.succ))
    (hv : ∀ k, Function.Injective (coord (v k)))
    (hp : ∀ k, (crossingTimes coord (p k)).Finite) :
    (crossingTimes coord (Path.concat v p)).Finite := by
  induction m with
  | zero =>
    rw [Path.concat_zero]
    exact crossingTimes_refl_finite coord (hv 0)
  | succ m ih =>
    rw [Path.concat_succ]
    exact crossingTimes_trans_finite coord _ _ (hv 0) (hv (Fin.last m).castSucc)
      (hv (Fin.last (m + 1)))
      (ih (v ∘ Fin.castSucc) (fun k => p k.castSucc)
        (fun k => hv k.castSucc) (fun k => hp k.castSucc)) (hp (Fin.last m))

end TarchaBraids.NormalForm
end

/- UnorderedPolygonalLift -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open unitInterval
open BraidsLinksMCG

noncomputable section

namespace TarchaBraids.NormalForm

def realCoordinates {n : ℕ} (z : OrderedConfig n) : Fin n → ℝ :=
  fun j => (z.val j).re

theorem baseOrdered_real_injective (n : ℕ) :
    Function.Injective (realCoordinates (baseOrdered n)) := by
  intro i j hij
  have h : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 := by
    simpa only [realCoordinates, baseOrdered, Complex.add_re,
      Complex.natCast_re, Complex.one_re] using hij
  exact Fin.ext (by exact_mod_cast add_right_cancel h)

theorem base_fiber_real_injective {n : ℕ} (b : OrderedConfig n)
    (hb : configProj n b = baseUnordered n) :
    Function.Injective (realCoordinates b) := by
  obtain ⟨g, hg⟩ := Quotient.exact hb.symm
  change b.val = (baseOrdered n).val ∘ g at hg
  intro i j hij
  apply g.injective
  apply baseOrdered_real_injective n
  simpa only [realCoordinates, hg, Function.comp_apply] using hij

theorem exists_finite_crossing_configuration_path {n : ℕ}
    {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (realCoordinates a))
    (hb : Function.Injective (realCoordinates b)) :
    ∃ q : Path a b, p.Homotopic q ∧
      (crossingTimes realCoordinates q).Finite := by
  obtain ⟨m, v, segments, hv, hsegments, h0, h1, hhom⟩ :=
    BraidNormalForm.exists_polygonal_configuration_path p ha hb
  refine ⟨(Path.concat v segments).cast h0 h1, hhom, ?_⟩
  change (crossingTimes realCoordinates (Path.concat v segments)).Finite
  apply crossingTimes_concat_finite realCoordinates v segments hv
  intro k
  have hfinite := lineMap_crossings_finite_on
    (v k.castSucc).val (v k.succ).val (hv k.castSucc) (Set.Icc 0 1)
  apply hfinite.subset
  rintro t ⟨i, j, hij, he⟩
  refine ⟨i, j, hij, ?_⟩
  change (((segments k) t).val i).re = (((segments k) t).val j).re at he
  rw [hsegments k t] at he
  exact he

/-- A continuous unordered loop has a collision-free ordered representative with
finitely many real-coordinate crossing times. -/
theorem exists_finite_crossing_lift {n : ℕ}
    (δ : Path (baseUnordered n) (baseUnordered n)) :
    ∃ (b : OrderedConfig n) (q : Path (baseOrdered n) b)
      (hb : configProj n b = baseUnordered n),
      Function.Injective (realCoordinates b) ∧
      (crossingTimes realCoordinates q).Finite ∧
      δ.Homotopic ((q.map (configProj n).continuous).cast rfl hb.symm) := by
  obtain ⟨Γ, hΓ, hzero⟩ := (configProj_isCoveringMap n).exists_path_lifts
    δ.toContinuousMap (baseOrdered n) δ.source
  have hlift : ∀ t, configProj n (Γ t) = δ t := fun t => congrFun hΓ t
  let b : OrderedConfig n := Γ 1
  let p : Path (baseOrdered n) b :=
    { toFun := Γ
      continuous_toFun := Γ.continuous
      source' := hzero
      target' := rfl }
  have hb : configProj n b = baseUnordered n := (hlift 1).trans δ.target
  have hreal := base_fiber_real_injective b hb
  obtain ⟨q, hpq, hq⟩ := exists_finite_crossing_configuration_path p
    (baseOrdered_real_injective n) hreal
  refine ⟨b, q, hb, hreal, hq, ?_⟩
  have hmap := (hpq.map (configProj n)).pathCast rfl hb.symm
  have he : ((p.map (configProj n).continuous).cast rfl hb.symm) = δ := by
    apply Path.ext
    funext t
    exact hlift t
  exact Eq.mp (congrArg (fun γ => γ.Homotopic
    ((q.map (configProj n).continuous).cast rfl hb.symm)) he) hmap

end TarchaBraids.NormalForm

end
end

/- CanonicalBaseConnectors -/
section
set_option autoImplicit false

open unitInterval
open BraidsLinksMCG

namespace BraidNormalForm

theorem base_real_injective (n : ℕ) :
    Function.Injective (fun i => ((baseOrdered n).val i).re) :=
  (baseOrdered_mem_identity_chamber n).injective

theorem canonical_base_approach_constant (n : ℕ) (t : I) :
    canonicalChamberApproach (baseOrdered n) (base_real_injective n) t = baseUnordered n := by
  have hs : sortingPermutation (baseOrdered n) (base_real_injective n) = Equiv.refl (Fin n) :=
    sorting_permutation_unique (fun i => ((baseOrdered n).val i).re)
      (sortingPermutation_strictMono (baseOrdered n) (base_real_injective n))
      (baseOrdered_mem_identity_chamber n)
  have he : chamberApproach (sortingPermutation (baseOrdered n) (base_real_injective n))
      (baseOrdered n) (sortingPermutation_strictMono _ _) t = baseOrdered n := by
    apply Subtype.ext
    change AffineMap.lineMap
      (relabelledBase (sortingPermutation (baseOrdered n) (base_real_injective n))).val
      (baseOrdered n).val (t : ℝ) = _
    rw [hs]
    change AffineMap.lineMap (baseOrdered n).val (baseOrdered n).val (t : ℝ) = _
    simp only [AffineMap.lineMap_same, AffineMap.const_apply]
  exact congrArg (configProj n) he

theorem canonical_fiber_approach_constant {n : ℕ} (z : OrderedConfig n)
    (hz : Function.Injective (fun i => (z.val i).re))
    (hb : configProj n z = baseUnordered n) (t : I) :
    canonicalChamberApproach z hz t = baseUnordered n := by
  obtain ⟨perm, hp⟩ := Quotient.exact hb.symm
  have he : z = relabelConfig perm (baseOrdered n) := Subtype.ext hp
  subst z
  have hpath := canonicalChamberApproach_relabel perm (baseOrdered n) (base_real_injective n)
  have hpoint := congrArg (fun γ => γ t) hpath
  exact hpoint.trans (canonical_base_approach_constant n t)

end BraidNormalForm
end

/- GlobalNormalFormAssembly -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval
open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

theorem simple_affine_has_word {n : ℕ} (hlocal : LocalAffineWordProperty n)
    {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (hu : ∀ t (v w : StrandPair n), realGap v (p t).val = 0 →
      realGap w (p t).val = 0 → v = w) : TraceHasWord p ha hb := by
  obtain ⟨m, t, ht0, ht1, _, hvertices, hchart⟩ :=
    simple_affine_chart_subdivision p ha hb hp hu
  let v : Fin (m + 1) → OrderedConfig n := p ∘ t
  let segments : (k : Fin m) → Path (v k.castSucc) (v k.succ) :=
    fun k => p.subpath (t k.castSucc) (t k.succ)
  have hseg : ∀ k, TraceHasWord (segments k) (hvertices k.castSucc) (hvertices k.succ) := by
    intro k
    exact hlocal (segments k) (hvertices k.castSucc) (hvertices k.succ)
      (affine_subpath p hp (t k.castSucc) (t k.succ)) (hchart k)
  have hword := trace_word_concat v segments hvertices hseg
  let h0 : a = v 0 := ((congrArg p ht0).trans p.source).symm
  let h1 : b = v (Fin.last m) := ((congrArg p ht1).trans p.target).symm
  have hcast := trace_word_cast (Path.concat v segments) h0 h1
    (hvertices 0) (hvertices (Fin.last m)) ha hb hword
  have hhom : p.Homotopic ((Path.concat v segments).cast h0 h1) := by
    have h := (Path.Homotopic.concat_subpath p t).symm.pathCast h0 h1
    have he : (p.subpath (t 0) (t (Fin.last m))).cast h0 h1 = p := by
      apply Path.ext
      funext s
      change p.subpath (t 0) (t (Fin.last m)) s = p s
      rw [ht0, ht1, Path.subpath_zero_one]
      rfl
    exact Eq.mp (congrArg (fun γ => γ.Homotopic
      ((Path.concat v segments).cast h0 h1)) he) h
  exact trace_word_homotopy ha hb hhom hcast

theorem affine_has_word {n : ℕ} (hlocal : LocalAffineWordProperty n)
    {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ)) :
    TraceHasWord p ha hb := by
  obtain ⟨c, q, r, hc, hq, hr, hqu, hru, _, _, hhom⟩ :=
    affine_path_has_simple_refinement p ha hb hp
  have hwq := simple_affine_has_word hlocal q ha hc hq hqu
  have hwr := simple_affine_has_word hlocal r hc hb hr hru
  exact trace_word_homotopy ha hb hhom (trace_word_trans q r ha hc hb hwq hwr)

theorem ordered_path_has_word {n : ℕ} (hlocal : LocalAffineWordProperty n)
    {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re)) : TraceHasWord p ha hb := by
  obtain ⟨m, v, segments, hv, hsegments, h0, h1, hhom⟩ :=
    exists_polygonal_configuration_path p ha hb
  have hseg : ∀ k, TraceHasWord (segments k) (hv k.castSucc) (hv k.succ) :=
    fun k => affine_has_word hlocal (segments k) (hv k.castSucc) (hv k.succ) (hsegments k)
  have hw := trace_word_concat v segments hv hseg
  exact trace_word_homotopy ha hb hhom (trace_word_cast (Path.concat v segments) h0 h1
    (hv 0) (hv (Fin.last m)) ha hb hw)

/-- Internal assembly: the only input is the local affine crossing-chart theorem. -/
theorem every_loop_has_word_of_local (n : ℕ) (hlocal : LocalAffineWordProperty n) :
    EveryLoopHasBraidWord n := by
  intro δ
  obtain ⟨Γ, hΓ, hzero⟩ := (configProj_isCoveringMap n).exists_path_lifts
    δ.toContinuousMap (baseOrdered n) δ.source
  have hlift : ∀ t, configProj n (Γ t) = δ t := fun t => congrFun hΓ t
  let b : OrderedConfig n := Γ 1
  let p : Path (baseOrdered n) b := {
    toFun := Γ
    continuous_toFun := Γ.continuous
    source' := hzero
    target' := rfl
  }
  have hb : configProj n b = baseUnordered n := (hlift 1).trans δ.target
  have hbr := TarchaBraids.NormalForm.base_fiber_real_injective b hb
  obtain ⟨w, hw⟩ := ordered_path_has_word hlocal p (base_real_injective n) hbr
  have hconst := basedTrace_constant_connectors (p.map (configProj n).continuous)
    (canonicalChamberApproach (baseOrdered n) (base_real_injective n))
    (canonicalChamberApproach b hbr) rfl hb
    (canonical_base_approach_constant n) (canonical_fiber_approach_constant b hbr hb)
  have h := hconst.symm.trans hw
  have he : ((p.map (configProj n).continuous).cast rfl hb.symm) = δ := by
    apply Path.ext
    funext t
    exact hlift t
  exact ⟨w, Eq.mp (congrArg (fun γ => γ.Homotopic (braidWordLoop n w)) he) h⟩

end BraidNormalForm
end

/- AdjacentChamberSwap -/
section
set_option autoImplicit false

open BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

private theorem adjacent_nat_swap_lt (a k l : ℕ) (hkl : k < l)
    (hex : k ≠ a ∨ l ≠ a + 1) :
    (if k = a then a + 1 else if k = a + 1 then a else k) <
      (if l = a then a + 1 else if l = a + 1 then a else l) := by
  split_ifs <;> omega

theorem adjacentSwap_val {n : ℕ} (i : Fin (n - 1)) (k : Fin n) :
    (adjacentSwap i k).val =
      if k.val = i.val then i.val + 1 else if k.val = i.val + 1 then i.val else k.val := by
  by_cases hk0 : k.val = i.val
  · have he : k = strandIdx i := Fin.ext hk0
    subst k
    simp only [adjacentSwap, Equiv.swap_apply_left, strandIdx, strandIdxSucc, ↓reduceIte]
  · by_cases hk1 : k.val = i.val + 1
    · have he : k = strandIdxSucc i := Fin.ext hk1
      subst k
      simp only [adjacentSwap, Equiv.swap_apply_right, strandIdx, strandIdxSucc,
        Nat.add_one_ne_self, ↓reduceIte]
    · rw [adjacentSwap, Equiv.swap_apply_of_ne_of_ne
        (fun h => hk0 (congrArg Fin.val h)) (fun h => hk1 (congrArg Fin.val h))]
      simp only [hk0, hk1, ↓reduceIte]

theorem adjacentSwap_preserves_other_order {n : ℕ} (i : Fin (n - 1))
    (k l : Fin n) (hkl : k < l) (hex : k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) :
    adjacentSwap i k < adjacentSwap i l := by
  have hn : k.val ≠ i.val ∨ l.val ≠ i.val + 1 := by
    rcases hex with hk | hl
    · exact Or.inl (fun h => hk (Fin.ext h))
    · exact Or.inr (fun h => hl (Fin.ext h))
  change (adjacentSwap i k).val < (adjacentSwap i l).val
  rw [adjacentSwap_val, adjacentSwap_val]
  exact adjacent_nat_swap_lt i.val k.val l.val hkl hn

theorem mem_chamber_after_adjacent_swap {n : ℕ} (i : Fin (n - 1))
    (z : OrderedConfig n)
    (hother : ∀ k l : Fin n, k < l → (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      (z.val k).re < (z.val l).re)
    (hpair : (z.val (strandIdxSucc i)).re < (z.val (strandIdx i)).re) :
    z.val ∈ realChamber (adjacentSwap i) := by
  intro k l hkl
  by_cases hp : k = strandIdx i ∧ l = strandIdxSucc i
  · rcases hp with ⟨rfl, rfl⟩
    simpa only [adjacentSwap, Equiv.swap_apply_left, Equiv.swap_apply_right] using hpair
  have hn : k ≠ strandIdx i ∨ l ≠ strandIdxSucc i := by tauto
  apply hother _ _ (adjacentSwap_preserves_other_order i k l hkl hn)
  by_cases hk : adjacentSwap i k = strandIdx i
  · apply Or.inr
    intro hl
    have hk' : k = strandIdxSucc i := (adjacentSwap i).injective (hk.trans (by
      exact (Equiv.swap_apply_right (strandIdx i) (strandIdxSucc i)).symm))
    have hl' : l = strandIdx i := (adjacentSwap i).injective (hl.trans (by
      exact (Equiv.swap_apply_left (strandIdx i) (strandIdxSucc i)).symm))
    have hval : k.val < l.val := hkl
    rw [hk', hl'] at hval
    change i.val + 1 < i.val at hval
    omega
  · exact Or.inl hk

end BraidNormalForm
end

/- PairChartGeometry -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

lemma pairChart_relabel {n : ℕ} (f : I → OrderedConfig n) (p : StrandPair n)
    (hp : PairChart f p univ) (perm : Equiv.Perm (Fin n)) :
    ∃ q : StrandPair n, PairChart (fun t => relabelConfig perm (f t)) q univ := by
  obtain ⟨q, hq⟩ := exists_relabelled_pair perm p
  refine ⟨q, ?_, ?_⟩
  · intro t _
    have hs := (hq q.val.1 q.val.2).mp (Or.inl ⟨rfl, rfl⟩)
    change ((f t).val (perm q.val.1)).im ≠ ((f t).val (perm q.val.2)).im
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hp.1 t (mem_univ t)
    · rw [h1, h2]
      exact (hp.1 t (mem_univ t)).symm
  · intro t _ k l hkl hex
    change ((f t).val (perm k)).re ≠ ((f t).val (perm l)).re
    apply hp.2 t (mem_univ t) (perm k) (perm l)
    · exact fun he => hkl (perm.injective he)
    · exact fun he => hex ((hq k l).mpr he)

lemma affine_relabel {n : ℕ} {a b : OrderedConfig n} (p : Path a b)
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (perm : Equiv.Perm (Fin n)) (t : I) :
    ((p.map (relabelConfig perm).continuous) t).val =
      AffineMap.lineMap (relabelConfig perm a).val (relabelConfig perm b).val (t : ℝ) := by
  funext k
  exact congrFun (hp t) (perm k)

/-- In sorted coordinates, a chart which actually crosses contains one
adjacent swap. Its endpoint chamber and crossing sign are consequences of the
chart, affineness, and real-distinct endpoints. -/
theorem sorted_pair_chart_geometry {n : ℕ} {a b : OrderedConfig n}
    (p : Path a b) (q : StrandPair n)
    (ha : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (hchart : PairChart p q univ)
    (hcross : ∃ t : I, realGap q (p t).val = 0) :
    ∃ i : Fin (n - 1), b.val ∈ realChamber (adjacentSwap i) ∧
      (∀ (t : I) (k l : Fin n), k < l → (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
        ((p t).val k).re < ((p t).val l).re) ∧
      ((∀ t : I, 0 < ((p t).val (strandIdxSucc i)).im - ((p t).val (strandIdx i)).im) ∨
       (∀ t : I, ((p t).val (strandIdxSucc i)).im - ((p t).val (strandIdx i)).im < 0)) := by
  have hc (k : Fin n) : Continuous (fun t : I => (p t).val k) :=
    (continuous_apply k).comp (continuous_subtype_val.comp p.continuous)
  have horder : ∀ (t : I) (k l : Fin n), k < l → (k ≠ q.val.1 ∨ l ≠ q.val.2) →
      ((p t).val k).re < ((p t).val l).re := by
    intro t k l hkl hex
    have hnot : ¬ selectedPair q k l := by
      rintro (⟨hk, hl⟩ | ⟨hk, hl⟩)
      · exact hex.elim (fun h => h hk) (fun h => h hl)
      · have hrev := q.property
        rw [hk, hl] at hkl
        exact (not_lt_of_ge hrev.le) hkl
    have hne : ∀ t : I, ((p t).val k).re ≠ ((p t).val l).re :=
      fun t => hchart.2 t (mem_univ t) k l (ne_of_lt hkl) hnot
    have h0 : ((p 0).val k).re < ((p 0).val l).re := by
      simpa only [p.source, Equiv.refl_apply] using ha hkl
    exact real_order_constant (Complex.continuous_re.comp (hc k))
      (Complex.continuous_re.comp (hc l)) hne h0 t
  obtain ⟨t₀, ht₀⟩ := hcross
  have hadj := crossing_pair_adjacent (p t₀).val q ht₀ (horder t₀)
  let i : Fin (n - 1) := ⟨q.val.1.val, by have h := q.val.2.isLt; omega⟩
  have hi : strandIdx i = q.val.1 := Fin.ext rfl
  have hj : strandIdxSucc i = q.val.2 := Fin.ext hadj.symm
  have horderI : ∀ (t : I) (k l : Fin n), k < l → (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
      ((p t).val k).re < ((p t).val l).re := by
    simpa only [hi, hj] using horder
  have hstart : realGap q a.val < 0 := by
    apply sub_neg.mpr
    exact ha q.property
  have hroot : realGap q (AffineMap.lineMap a.val b.val (t₀ : ℝ)) = 0 := by
    rw [← hp t₀]
    exact ht₀
  have hflip := affine_crossing_reverses_order a.val b.val q hstart (realGap_at_ne_zero hb q) t₀ hroot
  have hend : (b.val (strandIdxSucc i)).re < (b.val (strandIdx i)).re := by
    rw [hi, hj]
    exact sub_pos.mp hflip
  have hbC := mem_chamber_after_adjacent_swap i b
    (fun k l hkl hex => by simpa only [p.target] using horderI 1 k l hkl hex) hend
  refine ⟨i, hbC, horderI, ?_⟩
  have hne : ∀ t : I, ((p t).val (strandIdx i)).im ≠ ((p t).val (strandIdxSucc i)).im := by
    intro t
    rw [hi, hj]
    exact hchart.1 t (mem_univ t)
  rcases lt_or_gt_of_ne (hne 0) with hpos | hneg
  · left
    intro t
    exact sub_pos.mpr (real_order_constant (Complex.continuous_im.comp (hc (strandIdx i)))
      (Complex.continuous_im.comp (hc (strandIdxSucc i))) hne hpos t)
  · right
    intro t
    exact sub_neg.mpr (real_order_constant (Complex.continuous_im.comp (hc (strandIdxSucc i)))
      (Complex.continuous_im.comp (hc (strandIdx i))) (fun t => (hne t).symm) hneg t)

end BraidNormalForm
end

/- LocalPairWord -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set unitInterval BraidsLinksMCG TarchaBraids

namespace BraidNormalForm

lemma selectedPair_ordered_iff {n : ℕ} (p q : StrandPair n) :
    selectedPair p q.val.1 q.val.2 ↔ q = p := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · apply Subtype.ext
      exact Prod.ext h1 h2
    · have hq := q.property
      rw [h1, h2] at hq
      exact False.elim ((not_lt_of_ge p.property.le) hq)
  · intro h
    subst q
    exact Or.inl ⟨rfl, rfl⟩

lemma basedTrace_eq_of_pointwise {X : Type*} [TopologicalSpace X]
    {base a b c d : X} (ca : Path base a) (p : Path a b) (cb : Path base b)
    (cc : Path base c) (q : Path c d) (cd : Path base d)
    (hleft : ∀ t : I, ca t = cc t) (hmiddle : ∀ t : I, p t = q t)
    (hright : ∀ t : I, cb t = cd t) :
    basedTrace ca p cb = basedTrace cc q cd := by
  apply Path.ext
  funext t
  simp only [basedTrace, Path.trans_apply, Path.symm_apply]
  split_ifs <;> first | exact hleft _ | exact hmiddle _ | exact hright _

lemma canonical_trace_relabel {n : ℕ} {a b : OrderedConfig n} (p : Path a b)
    (perm : Equiv.Perm (Fin n))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) :
    basedTrace
      (canonicalChamberApproach (relabelConfig perm a) (relabel_real_injective perm a ha))
      ((p.map (relabelConfig perm).continuous).map (configProj n).continuous)
      (canonicalChamberApproach (relabelConfig perm b) (relabel_real_injective perm b hb)) =
    basedTrace (canonicalChamberApproach a ha) (p.map (configProj n).continuous)
      (canonicalChamberApproach b hb) := by
  apply basedTrace_eq_of_pointwise
  · intro t
    exact congrArg (fun γ => γ t) (canonicalChamberApproach_relabel perm a ha)
  · intro t
    exact configProj_relabel perm (p t)
  · intro t
    exact congrArg (fun γ => γ t) (canonicalChamberApproach_relabel perm b hb)

lemma letter_homotopic_singleton {n : ℕ} (a : BraidLetter n) :
    (braidLetterLoop n a).Homotopic (braidWordLoop n [a]) := by
  apply Path.Homotopic.Quotient.eq.mp
  simp only [braidWordLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans]

lemma no_crossing_has_word {n : ℕ} {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hreal : ∀ t : I, Function.Injective (fun k => ((p t).val k).re)) :
    TraceHasWord p ha hb :=
  ⟨[], no_crossing_canonical_trace_null p ha hb hreal⟩

/-- An affine path in one good chart, already sorted at its source, is either
crossing-free or one signed adjacent half-twist. -/
theorem sorted_good_chart_has_word {n : ℕ} {a b : OrderedConfig n} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (ham : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (hchart : GoodChart p univ) : TraceHasWord p ha hb := by
  classical
  rcases hchart with hnone | ⟨q, hq⟩
  · exact no_crossing_has_word p ha hb (fun t => hnone t (mem_univ t))
  by_cases hcross : ∃ t : I, realGap q (p t).val = 0
  · obtain ⟨i, hbm, horder, hsign⟩ := sorted_pair_chart_geometry p q ham hb hp hq hcross
    rcases hsign with hpos | hneg
    · refine ⟨[⟨i, .positive⟩], ?_⟩
      exact (positive_canonical_crossing_trace p i ha hb ham hbm horder hpos).trans
        (letter_homotopic_singleton (⟨i, .positive⟩ : BraidLetter n))
    · refine ⟨[⟨i, .negative⟩], ?_⟩
      exact (negative_canonical_crossing_trace p i ha hb ham hbm horder hneg).trans
        (letter_homotopic_singleton (⟨i, .negative⟩ : BraidLetter n))
  · apply no_crossing_has_word p ha hb
    intro t
    apply (real_injective_iff_gaps _).mpr
    intro r hr
    by_cases he : r = q
    · subst r
      exact hcross ⟨t, hr⟩
    · have hnot : ¬ selectedPair q r.val.1 r.val.2 :=
        fun h => he ((selectedPair_ordered_iff q r).mp h)
      exact hq.2 t (mem_univ t) r.val.1 r.val.2 (ne_of_lt r.property) hnot
        (sub_eq_zero.mp hr)

/-- The local affine normal-form property is unconditional: sorting is only
an internal relabelling, whose projected canonical connectors are unchanged. -/
theorem local_affine_word_property (n : ℕ) : LocalAffineWordProperty n := by
  intro a b p ha hb hp hchart
  let perm := sortingPermutation a ha
  let q := p.map (relabelConfig perm).continuous
  have ha' := relabel_real_injective perm a ha
  have hb' := relabel_real_injective perm b hb
  have ham : (relabelConfig perm a).val ∈ realChamber (Equiv.refl (Fin n)) := by
    change StrictMono (fun k => (a.val (perm k)).re)
    exact sortingPermutation_strictMono a ha
  have hqAffine : ∀ t : I, (q t).val =
      AffineMap.lineMap (relabelConfig perm a).val (relabelConfig perm b).val (t : ℝ) :=
    affine_relabel p hp perm
  have hqChart : GoodChart q univ := by
    rcases hchart with hnone | ⟨r, hr⟩
    · left
      intro t _
      exact (hnone t (mem_univ t)).comp perm.injective
    · right
      exact pairChart_relabel p r hr perm
  obtain ⟨w, hw⟩ := sorted_good_chart_has_word q ha' hb' ham hqAffine hqChart
  refine ⟨w, ?_⟩
  exact Eq.mp (congrArg (fun γ => γ.Homotopic (braidWordLoop n w))
    (canonical_trace_relabel p perm ha hb)) hw

end BraidNormalForm
end

/- EveryLoopNormalForm -/
section
set_option autoImplicit false

namespace TarchaBraids

theorem every_loop_homotopic_braidWord_v1 (n : ℕ) : EveryLoopHasBraidWord n :=
  BraidNormalForm.every_loop_has_word_of_local n (BraidNormalForm.local_affine_word_property n)

end TarchaBraids
end

theorem solution (n : ℕ) : TarchaBraids.EveryLoopHasBraidWord n :=
  TarchaBraids.every_loop_homotopic_braidWord_v1 n
