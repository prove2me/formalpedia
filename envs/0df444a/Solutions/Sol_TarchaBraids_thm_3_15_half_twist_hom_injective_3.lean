-- Prove2me | solution 3 for TarchaBraids.thm_3_15_half_twist_hom_injective
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-04T19:06:11.761956+00:00
-- url     : https://prove2.me/submissions/d7309d15-e9d7-4353-876b-a93a95dd8602

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1

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

/- ReferenceRealTime -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

noncomputable def signedReference (n : ℕ) (i : Fin n) (s : BraidLetterSign) :
    Path (baseOrdered (n + 1)) (referenceEnd (n + 1) i) :=
  match s with
  | .positive => positiveReference (n + 1) i
  | .negative => negativeReference (n + 1) i

theorem positiveReference_real_gap (n : ℕ) (i : Fin n) (t : I) :
    ((positiveReference (n + 1) i t).val i.succ).re -
      ((positiveReference (n + 1) i t).val i.castSucc).re = Real.cos (Real.pi * (t : ℝ)) := by
  change (halfTwistFun (n + 1) i (t : ℝ) (strandIdxSucc i)).re -
    (halfTwistFun (n + 1) i (t : ℝ) (strandIdx i)).re = _
  rw [halfTwistFun_of_eq_succ (t : ℝ) (by simp [strandIdxSucc]) (by simp [strandIdxSucc]),
    halfTwistFun_of_eq (t : ℝ) (by simp [strandIdx]), twistPoint_re, twistPoint_re]
  ring

theorem negativeReference_real_gap (n : ℕ) (i : Fin n) (t : I) :
    ((negativeReference (n + 1) i t).val i.succ).re -
      ((negativeReference (n + 1) i t).val i.castSucc).re = Real.cos (Real.pi * (t : ℝ)) := by
  have h := positiveReference_real_gap n i (unitInterval.symm t)
  change ((positiveReference (n + 1) i (unitInterval.symm t)).val
      (adjacentSwap (n := n + 1) i i.succ)).re -
    ((positiveReference (n + 1) i (unitInterval.symm t)).val
      (adjacentSwap (n := n + 1) i i.castSucc)).re = _
  have hi : strandIdx (n := n + 1) i = i.castSucc := rfl
  have hj : strandIdxSucc (n := n + 1) i = i.succ := rfl
  rw [adjacentSwap, hi, hj, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have he : Real.pi * ((unitInterval.symm t : I) : ℝ) = Real.pi - Real.pi * (t : ℝ) := by
    change Real.pi * (1 - (t : ℝ)) = _
    ring
  rw [he, Real.cos_pi_sub] at h
  linarith

theorem signedReference_real_gap (n : ℕ) (i : Fin n) (s : BraidLetterSign) (t : I) :
    ((signedReference n i s t).val i.succ).re -
      ((signedReference n i s t).val i.castSucc).re = Real.cos (Real.pi * (t : ℝ)) := by
  cases s
  · exact positiveReference_real_gap n i t
  · exact negativeReference_real_gap n i t

theorem signedReference_other_order (n : ℕ) (i : Fin n) (s : BraidLetterSign) (t : I)
    (k l : Fin (n + 1)) (hkl : k < l) (hex : k ≠ i.castSucc ∨ l ≠ i.succ) :
    ((signedReference n i s t).val k).re < ((signedReference n i s t).val l).re := by
  cases s
  · exact positiveReference_real_order (n + 1) i t k l hkl hex
  · exact negativeReference_real_order (n + 1) i t k l hkl hex

theorem cos_pi_mul_pos {t : I} (ht : (t : ℝ) < 1 / 2) :
    0 < Real.cos (Real.pi * (t : ℝ)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, t.property.1]
  · nlinarith [Real.pi_pos]

theorem cos_pi_mul_neg {t : I} (ht : 1 / 2 < (t : ℝ)) :
    Real.cos (Real.pi * (t : ℝ)) < 0 := by
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos, t.property.2]

theorem signedReference_before (n : ℕ) (i : Fin n) (s : BraidLetterSign) (t : I)
    (ht : (t : ℝ) < 1 / 2) :
    (signedReference n i s t).val ∈ realChamber (Equiv.refl (Fin (n + 1))) := by
  intro k l hkl
  change ((signedReference n i s t).val k).re < ((signedReference n i s t).val l).re
  by_cases h : k = i.castSucc ∧ l = i.succ
  · rcases h with ⟨rfl, rfl⟩
    have hgap := signedReference_real_gap n i s t
    linarith [cos_pi_mul_pos ht]
  · exact signedReference_other_order n i s t k l hkl (by tauto)

theorem signedReference_after (n : ℕ) (i : Fin n) (s : BraidLetterSign) (t : I)
    (ht : 1 / 2 < (t : ℝ)) :
    (signedReference n i s t).val ∈ realChamber (adjacentSwap (n := n + 1) i) := by
  apply mem_chamber_after_adjacent_swap (n := n + 1) i (signedReference n i s t)
  · exact signedReference_other_order n i s t
  · have hgap := signedReference_real_gap n i s t
    apply sub_neg.mp
    change ((signedReference n i s t).val i.succ).re -
      ((signedReference n i s t).val i.castSucc).re < 0
    rw [hgap]
    exact cos_pi_mul_neg ht

theorem realChamber_real_injective {n : ℕ} (perm : Equiv.Perm (Fin n))
    {a : Fin n → ℂ} (ha : a ∈ realChamber perm) :
    Function.Injective (fun k => (a k).re) := by
  intro k l hkl
  have he : (a (perm (perm.symm k))).re = (a (perm (perm.symm l))).re := by
    simpa only [Equiv.apply_symm_apply] using hkl
  exact perm.symm.injective (ha.injective he)

theorem signedReference_real_injective (n : ℕ) (i : Fin n) (s : BraidLetterSign)
    (t : I) (ht : (t : ℝ) ≠ 1 / 2) :
    Function.Injective (fun k => ((signedReference n i s t).val k).re) := by
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · exact realChamber_real_injective _ (signedReference_before n i s t hlt)
  · exact realChamber_real_injective _ (signedReference_after n i s t hgt)

noncomputable def halfTime : I := ⟨1 / 2, by constructor <;> norm_num⟩

theorem signedReference_mid_pair (n : ℕ) (i : Fin n) (s : BraidLetterSign) :
    ((signedReference n i s halfTime).val i.castSucc).re =
      ((signedReference n i s halfTime).val i.succ).re := by
  have h := signedReference_real_gap n i s halfTime
  have he : Real.pi * ((halfTime : I) : ℝ) = Real.pi / 2 := by
    change Real.pi * (1 / 2) = Real.pi / 2
    ring
  rw [he, Real.cos_pi_div_two] at h
  exact (sub_eq_zero.mp h).symm

theorem signedReference_real_crossing_iff (n : ℕ) (i : Fin n) (s : BraidLetterSign)
    (t : I) :
    (¬ Function.Injective (fun k => ((signedReference n i s t).val k).re)) ↔
      (t : ℝ) = 1 / 2 := by
  constructor
  · intro h
    by_contra ht
    exact h (signedReference_real_injective n i s t ht)
  · intro ht hinj
    have htime : t = halfTime := Subtype.ext ht
    rw [htime] at hinj
    have h := hinj (signedReference_mid_pair n i s)
    have hval := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hval
    omega

end BraidConverse
end

/- NullHomotopyLift -/
section
set_option autoImplicit false

open unitInterval

namespace BraidConverse

theorem exists_nullhomotopic_loop_lift {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (hf : IsCoveringMap f) (a : E)
    (p : Path (f a) (f a)) (hp : p.Homotopic (Path.refl (f a))) :
    ∃ q : Path a a, q.map hf.continuous = p ∧ q.Homotopic (Path.refl a) := by
  let lift := hf.liftPath p.toContinuousMap a p.source
  have hzero : lift 0 = a := hf.liftPath_zero p.toContinuousMap a p.source
  have hone : lift 1 = a := by
    have h := hf.liftPath_apply_one_eq_of_homotopicRel hp a p.source
      (show (Path.refl (f a)).toContinuousMap 0 = f a from rfl)
    change lift 1 = (hf.liftPath (.const I (f a)) a rfl) 1 at h
    exact h.trans (congrArg (fun v : C(I, E) => v 1) (hf.liftPath_const (e := a) rfl))
  let q : Path a a :=
    { toFun := lift
      continuous_toFun := lift.continuous
      source' := hzero
      target' := hone }
  have hmap : q.map hf.continuous = p := by
    apply Path.ext
    funext t
    exact congrFun (hf.liftPath_lifts p.toContinuousMap a p.source) t
  refine ⟨q, hmap, ?_⟩
  apply (hf.homotopicRel_iff_comp (f₀ := q.toContinuousMap)
    (f₁ := (Path.refl a).toContinuousMap)
    ⟨0, Or.inl rfl, q.source⟩).mpr
  change (q.map hf.continuous).Homotopic ((Path.refl a).map hf.continuous)
  have hrefl : (Path.refl a).map hf.continuous = Path.refl (f a) := rfl
  simpa only [hmap, hrefl] using hp

theorem unordered_null_loop_lift (n : ℕ)
    (p : Path (BraidsLinksMCG.baseUnordered n) (BraidsLinksMCG.baseUnordered n))
    (hp : p.Homotopic (Path.refl (BraidsLinksMCG.baseUnordered n))) :
    ∃ q : Path (BraidsLinksMCG.baseOrdered n) (BraidsLinksMCG.baseOrdered n),
      q.map (BraidsLinksMCG.configProj n).continuous = p ∧
      q.Homotopic (Path.refl (BraidsLinksMCG.baseOrdered n)) :=
  exists_nullhomotopic_loop_lift (BraidsLinksMCG.configProj_isCoveringMap n)
    (BraidsLinksMCG.baseOrdered n) p hp

end BraidConverse
end

/- OrderedWordLift -/
section
set_option autoImplicit false

open unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

noncomputable section

namespace BraidConverse

def wordPermutation {n : ℕ} : List (BraidLetter (n + 1)) → Equiv.Perm (Fin (n + 1))
  | [] => 1
  | a :: w => adjacentSwap a.index * wordPermutation w

def wordEnd {n : ℕ} (w : List (BraidLetter (n + 1))) : OrderedConfig (n + 1) :=
  relabelConfig (wordPermutation w) (baseOrdered (n + 1))

lemma wordEnd_nil (n : ℕ) : wordEnd ([] : List (BraidLetter (n + 1))) = baseOrdered (n + 1) := rfl

lemma wordEnd_cons {n : ℕ} (a : BraidLetter (n + 1)) (w : List (BraidLetter (n + 1))) :
    wordEnd (a :: w) = relabelConfig (wordPermutation w) (referenceEnd (n + 1) a.index) := by
  exact congrArg (relabelConfig (wordPermutation w)) (relabel_base_referenceEnd (n + 1) a.index)

lemma wordEnd_projection {n : ℕ} (w : List (BraidLetter (n + 1))) :
    configProj (n + 1) (wordEnd w) = baseUnordered (n + 1) :=
  configProj_relabel (wordPermutation w) (baseOrdered (n + 1))

def letterAfter {n : ℕ} (w : List (BraidLetter (n + 1))) (a : BraidLetter (n + 1)) :
    Path (wordEnd w) (wordEnd (a :: w)) :=
  ((signedReference n a.index a.sign).map (relabelConfig (wordPermutation w)).continuous).cast
    rfl (wordEnd_cons a w)

def orderedWordLift {n : ℕ} (w : List (BraidLetter (n + 1))) :
    Path (baseOrdered (n + 1)) (wordEnd w) :=
  match w with
  | [] => (Path.refl (baseOrdered (n + 1))).cast rfl (wordEnd_nil n)
  | a :: w => (orderedWordLift w).trans (letterAfter w a)

theorem letterAfter_projection {n : ℕ} (w : List (BraidLetter (n + 1)))
    (a : BraidLetter (n + 1)) :
    ((letterAfter w a).map (configProj (n + 1)).continuous).cast
      (wordEnd_projection w).symm (wordEnd_projection (a :: w)).symm =
        braidLetterLoop (n + 1) a := by
  apply Path.ext
  funext t
  change configProj (n + 1)
    (relabelConfig (wordPermutation w) (signedReference n a.index a.sign t)) = _
  rw [configProj_relabel]
  rcases a with ⟨i, sign⟩
  cases sign
  · exact congrArg (fun p : Path (baseUnordered (n + 1)) (baseUnordered (n + 1)) => p t)
      (positiveReference_projection (n + 1) i)
  · exact congrArg (fun p : Path (baseUnordered (n + 1)) (baseUnordered (n + 1)) => p t)
      (negativeReference_projection (n + 1) i)

theorem orderedWordLift_projection {n : ℕ} (w : List (BraidLetter (n + 1))) :
    ((orderedWordLift w).map (configProj (n + 1)).continuous).cast
      rfl (wordEnd_projection w).symm = braidWordLoop (n + 1) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hm := congrArg (fun p => p.cast rfl (wordEnd_projection (a :: w)).symm)
      (Path.map_trans (orderedWordLift w) (letterAfter w a) (configProj (n + 1)).continuous)
    have hc := Path.cast_trans ((orderedWordLift w).map (configProj (n + 1)).continuous)
      ((letterAfter w a).map (configProj (n + 1)).continuous) rfl
      (wordEnd_projection w).symm (wordEnd_projection (a :: w)).symm
    exact hm.trans (hc.trans (congrArg₂ Path.trans ih (letterAfter_projection w a)))

end BraidConverse

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

/- OrderedWordTime -/
section
set_option autoImplicit false

open unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

noncomputable section

namespace BraidConverse

def leftTime (t : I) (ht : (t : ℝ) ≤ 1 / 2) : I :=
  ⟨2 * t, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

def rightTime (t : I) (ht : 1 / 2 ≤ (t : ℝ)) : I :=
  ⟨2 * t - 1, by constructor <;> nlinarith [t.property.1, t.property.2]⟩

theorem orderedWordLift_left {n : ℕ} (a : BraidLetter (n + 1))
    (w : List (BraidLetter (n + 1))) (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    orderedWordLift (a :: w) t = orderedWordLift w (leftTime t ht) := by
  change ((orderedWordLift w).trans (letterAfter w a)) t = _
  rw [Path.trans_apply, dif_pos ht]
  rfl

theorem orderedWordLift_right {n : ℕ} (a : BraidLetter (n + 1))
    (w : List (BraidLetter (n + 1))) (t : I) (ht : 1 / 2 ≤ (t : ℝ)) :
    orderedWordLift (a :: w) t = letterAfter w a (rightTime t ht) := by
  change ((orderedWordLift w).trans (letterAfter w a)) t = _
  calc
    _ = ((orderedWordLift w).trans (letterAfter w a)).extend (t : ℝ) :=
      (Path.extend_extends' _ t).symm
    _ = (letterAfter w a).extend (2 * t - 1) :=
      Path.extend_trans_of_half_le _ _ ht
    _ = _ := Path.extend_extends' _ (rightTime t ht)

theorem orderedWordLift_generic_after_last {n : ℕ} (w : List (BraidLetter (n + 1)))
    (t : I) (ht : 3 / 4 < (t : ℝ)) :
    Function.Injective (fun i => ((orderedWordLift w t).val i).re) := by
  cases w with
  | nil => exact base_real_injective (n + 1)
  | cons a w =>
    have hh : 1 / 2 ≤ (t : ℝ) := by linarith
    rw [orderedWordLift_right a w t hh]
    have hlocal : (rightTime t hh : ℝ) ≠ 1 / 2 := by
      change 2 * (t : ℝ) - 1 ≠ 1 / 2
      linarith
    exact (signedReference_real_injective n a.index a.sign (rightTime t hh) hlocal).comp
      (wordPermutation w).injective

theorem orderedWordLift_generic_around_join {n : ℕ} (a : BraidLetter (n + 1))
    (w : List (BraidLetter (n + 1))) (t : I)
    (ht0 : 3 / 8 < (t : ℝ)) (ht1 : (t : ℝ) < 3 / 4) :
    Function.Injective (fun i => ((orderedWordLift (a :: w) t).val i).re) := by
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [orderedWordLift_left a w t ht]
    apply orderedWordLift_generic_after_last
    change 3 / 4 < 2 * (t : ℝ)
    linarith
  · have hh : 1 / 2 ≤ (t : ℝ) := le_of_not_ge ht
    rw [orderedWordLift_right a w t hh]
    have hlocal : (rightTime t hh : ℝ) ≠ 1 / 2 := by
      change 2 * (t : ℝ) - 1 ≠ 1 / 2
      linarith
    exact (signedReference_real_injective n a.index a.sign (rightTime t hh) hlocal).comp
      (wordPermutation w).injective

end BraidConverse

end
end

/- PermutationSorting -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

namespace BraidConverse.PermutationSorting

abbrev Permutation (n : ℕ) := Equiv.Perm (Fin (n + 1))

def adjacent (n : ℕ) (i : Fin n) : Permutation n := Equiv.swap i.castSucc i.succ

def swapAt {n : ℕ} (p : Permutation n) (i : Fin n) : Permutation n := p * adjacent n i

def Descent {n : ℕ} (p : Permutation n) (i : Fin n) : Prop := p i.succ < p i.castSucc

def Step {n : ℕ} (p q : Permutation n) : Prop := ∃ i : Fin n, Descent p i ∧ q = swapAt p i

def LexLess {n : ℕ} (p q : Permutation n) : Prop :=
  (toLex (fun k => p k) : Lex (Fin (n + 1) → Fin (n + 1))) < toLex (fun k => q k)

lemma swapAt_apply {n : ℕ} (p : Permutation n) (i : Fin n) (k : Fin (n + 1)) :
    swapAt p i k = p (Equiv.swap i.castSucc i.succ k) := rfl

lemma swapAt_left {n : ℕ} (p : Permutation n) (i : Fin n) :
    swapAt p i i.castSucc = p i.succ := by
  rw [swapAt_apply, Equiv.swap_apply_left]

lemma swapAt_right {n : ℕ} (p : Permutation n) (i : Fin n) :
    swapAt p i i.succ = p i.castSucc := by
  rw [swapAt_apply, Equiv.swap_apply_right]

lemma swapAt_other {n : ℕ} (p : Permutation n) (i : Fin n) (k : Fin (n + 1))
    (hk0 : k ≠ i.castSucc) (hk1 : k ≠ i.succ) : swapAt p i k = p k := by
  rw [swapAt_apply, Equiv.swap_apply_of_ne_of_ne hk0 hk1]

lemma swapAt_lex_decreases {n : ℕ} (p : Permutation n) (i : Fin n) (hi : Descent p i) :
    LexLess (swapAt p i) p := by
  refine ⟨i.castSucc, ?_, ?_⟩
  · intro k hk
    apply swapAt_other p i k (ne_of_lt hk)
    have his : i.castSucc < i.succ := Nat.lt_succ_self i.val
    exact ne_of_lt (hk.trans his)
  · change swapAt p i i.castSucc < p i.castSucc
    rw [swapAt_left]
    exact hi

lemma lexLess_wellFounded (n : ℕ) : WellFounded (@LexLess n) := by
  have h : WellFounded ((· < ·) :
      Lex (Fin (n + 1) → Fin (n + 1)) → Lex (Fin (n + 1) → Fin (n + 1)) → Prop) :=
    Finite.wellFounded_of_trans_of_irrefl _
  exact InvImage.wf (fun p : Permutation n => toLex (fun k => p k)) h

/-- Every descending adjacent swap strictly decreases the finite lexicographic order. -/
theorem step_wellFounded (n : ℕ) : WellFounded (fun q p : Permutation n => Step p q) := by
  apply Subrelation.wf (r := @LexLess n) ?_ (lexLess_wellFounded n)
  intro q p h
  obtain ⟨i, hi, rfl⟩ := h
  exact swapAt_lex_decreases p i hi

lemma eq_one_of_no_descent {n : ℕ} (p : Permutation n) (h : ∀ i : Fin n, ¬ Descent p i) :
    p = 1 := by
  have hm : StrictMono p := Fin.strictMono_iff_lt_succ.mpr (fun i => by
    have hle : p i.castSucc ≤ p i.succ := le_of_not_gt (h i)
    have hne : p i.castSucc ≠ p i.succ := by
      intro he
      have hidx : i.castSucc < i.succ := Nat.lt_succ_self i.val
      exact (ne_of_lt hidx) (p.injective he)
    exact lt_of_le_of_ne hle hne)
  apply Equiv.ext
  intro i
  exact hm.apply_eq

lemma exists_descent_of_ne_one {n : ℕ} (p : Permutation n) (hp : p ≠ 1) :
    ∃ i : Fin n, Descent p i := by
  classical
  by_contra h
  push Not at h
  exact hp (eq_one_of_no_descent p h)

/-- Left accumulation agrees with the algebraic word convention used by the
checked path normal form: each later crossing is prepended. -/
def WeightedStep {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (x y : Permutation n × G) : Prop :=
  ∃ i : Fin n, Descent x.1 i ∧ y.1 = swapAt x.1 i ∧ y.2 = (g i)⁻¹ * x.2

theorem weightedStep_wellFounded {n : ℕ} {G : Type*} [Group G] (g : Fin n → G) :
    WellFounded (fun y x => WeightedStep g x y) := by
  have h : WellFounded (fun y x : Permutation n × G => LexLess y.1 x.1) :=
    InvImage.wf Prod.fst (lexLess_wellFounded n)
  apply Subrelation.wf (r := fun y x : Permutation n × G => LexLess y.1 x.1) ?_ h
  intro y x hy
  obtain ⟨i, hi, he, _⟩ := hy
  rw [he]
  exact swapAt_lex_decreases x.1 i hi

end BraidConverse.PermutationSorting
end

/- SortingCriticalPairs -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

namespace BraidConverse.PermutationSorting

lemma far_descent_preserved {n : ℕ} (p : Permutation n) (i j : Fin n)
    (hfar : i.val + 1 < j.val) :
    (Descent p i → Descent (swapAt p j) i) ∧
      (Descent p j → Descent (swapAt p i) j) := by
  have hi : i.castSucc < i.succ := Nat.lt_succ_self i.val
  have hj : j.castSucc < j.succ := Nat.lt_succ_self j.val
  have hsep : i.succ < j.castSucc := hfar
  constructor
  · intro h
    change swapAt p j i.succ < swapAt p j i.castSucc
    rw [swapAt_other p j i.succ (ne_of_lt hsep) (ne_of_lt (hsep.trans hj)),
      swapAt_other p j i.castSucc (ne_of_lt (hi.trans hsep))
        (ne_of_lt (hi.trans (hsep.trans hj)))]
    exact h
  · intro h
    change swapAt p i j.succ < swapAt p i j.castSucc
    rw [swapAt_other p i j.succ (ne_of_gt (hi.trans (hsep.trans hj)))
        (ne_of_gt (hsep.trans hj)),
      swapAt_other p i j.castSucc (ne_of_gt (hi.trans hsep)) (ne_of_gt hsep)]
    exact h

lemma adjacent_far_commute {n : ℕ} (i j : Fin n) (hfar : i.val + 1 < j.val) :
    adjacent n i * adjacent n j = adjacent n j * adjacent n i := by
  have hi : i.castSucc < i.succ := Nat.lt_succ_self i.val
  have hj : j.castSucc < j.succ := Nat.lt_succ_self j.val
  have hsep : i.succ < j.castSucc := hfar
  unfold adjacent
  rw [Equiv.mul_swap_eq_swap_mul,
    Equiv.swap_apply_of_ne_of_ne (ne_of_gt (hi.trans hsep)) (ne_of_gt hsep),
    Equiv.swap_apply_of_ne_of_ne (ne_of_gt (hi.trans (hsep.trans hj)))
      (ne_of_gt (hsep.trans hj))]

lemma swapAt_far_commute {n : ℕ} (p : Permutation n) (i j : Fin n)
    (hfar : i.val + 1 < j.val) : swapAt (swapAt p i) j = swapAt (swapAt p j) i := by
  simpa only [swapAt, mul_assoc] using
    congrArg (fun v : Permutation n => p * v) (adjacent_far_commute i j hfar)

lemma swap_braid {A : Type*} [DecidableEq A] (x y z : A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Equiv.swap x y * Equiv.swap y z * Equiv.swap x y =
      Equiv.swap y z * Equiv.swap x y * Equiv.swap y z := by
  have hl := Equiv.swap_mul_swap_mul_swap (x := z) (y := y) (z := x) hyz.symm hxz.symm
  rw [Equiv.swap_comm y x, Equiv.swap_comm z y] at hl
  have hr := Equiv.swap_mul_swap_mul_swap (x := x) (y := y) (z := z) hxy hxz
  rw [Equiv.swap_comm z x] at hr
  exact hl.trans hr.symm

lemma adjacent_braid {n : ℕ} (i j : Fin n) (hij : j.val = i.val + 1) :
    adjacent n i * adjacent n j * adjacent n i =
      adjacent n j * adjacent n i * adjacent n j := by
  have hy : j.castSucc = i.succ := Fin.ext hij
  have hxy : i.castSucc < i.succ := Nat.lt_succ_self i.val
  have hyz : i.succ < j.succ := by rw [← hy]; exact Nat.lt_succ_self j.val
  unfold adjacent
  rw [hy]
  exact swap_braid i.castSucc i.succ j.succ (ne_of_lt hxy) (ne_of_lt hyz)
    (ne_of_lt (hxy.trans hyz))

lemma swapAt_braid {n : ℕ} (p : Permutation n) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    swapAt (swapAt (swapAt p i) j) i = swapAt (swapAt (swapAt p j) i) j := by
  simpa only [swapAt, mul_assoc] using
    congrArg (fun v : Permutation n => p * v) (adjacent_braid i j hij)

/-- Two adjacent descents involve three labels in strictly decreasing order.
Both length-three sorting paths therefore exist and meet. -/
theorem adjacent_descent_diamond {n : ℕ} (p : Permutation n) (i j : Fin n)
    (hij : j.val = i.val + 1) (hi : Descent p i) (hj : Descent p j) :
    Descent (swapAt p i) j ∧ Descent (swapAt (swapAt p i) j) i ∧
      Descent (swapAt p j) i ∧ Descent (swapAt (swapAt p j) i) j := by
  have hy : j.castSucc = i.succ := Fin.ext hij
  have hxy : i.castSucc < i.succ := Nat.lt_succ_self i.val
  have hyz : i.succ < j.succ := by rw [← hy]; exact Nat.lt_succ_self j.val
  have hxj : i.castSucc < j.castSucc := by rw [hy]; exact hxy
  have hxz := hxy.trans hyz
  have hj' : p j.succ < p i.succ := by simpa only [Descent, hy] using hj
  refine ⟨?_, ?_, ?_, ?_⟩
  · change swapAt p i j.succ < swapAt p i j.castSucc
    rw [hy, swapAt_right,
      swapAt_other p i j.succ (ne_of_gt hxz) (ne_of_gt hyz)]
    exact hj'.trans hi
  · change swapAt (swapAt p i) j i.succ < swapAt (swapAt p i) j i.castSucc
    rw [← hy, swapAt_left,
      swapAt_other (swapAt p i) j i.castSucc (ne_of_lt hxj) (ne_of_lt hxz),
      swapAt_other p i j.succ (ne_of_gt hxz) (ne_of_gt hyz), swapAt_left]
    exact hj'
  · change swapAt p j i.succ < swapAt p j i.castSucc
    rw [← hy, swapAt_left,
      swapAt_other p j i.castSucc (ne_of_lt hxj) (ne_of_lt hxz)]
    exact hj'.trans hi
  · change swapAt (swapAt p j) i j.succ < swapAt (swapAt p j) i j.castSucc
    rw [hy, swapAt_right,
      swapAt_other (swapAt p j) i j.succ (ne_of_gt hxz) (ne_of_gt hyz),
      swapAt_right, swapAt_other p j i.castSucc (ne_of_lt hxj) (ne_of_lt hxz)]
    simpa only [Descent, hy] using hi

end BraidConverse.PermutationSorting
end

/- SignedBraidMoves -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

namespace BraidConverse

variable {G : Type*} [Group G] {a b : G}

lemma braid_mixed_ppn (h : a * b * a = b * a * b) :
    a * b * a⁻¹ = b⁻¹ * a * b := by
  have hh := congrArg (fun x : G => b⁻¹ * x * a⁻¹) h
  convert hh.symm using 1 <;> group

lemma braid_mixed_npp (h : a * b * a = b * a * b) :
    a⁻¹ * b * a = b * a * b⁻¹ := by
  have hh := congrArg (fun x : G => a⁻¹ * x * b⁻¹) h
  convert hh.symm using 1 <;> group

lemma braid_mixed_pnn (h : a * b * a = b * a * b) :
    a * b⁻¹ * a⁻¹ = b⁻¹ * a⁻¹ * b := by
  have hh := congrArg (fun x : G => x⁻¹) (braid_mixed_ppn h)
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh

lemma braid_mixed_nnp (h : a * b * a = b * a * b) :
    a⁻¹ * b⁻¹ * a = b * a⁻¹ * b⁻¹ := by
  have hh := congrArg (fun x : G => x⁻¹) (braid_mixed_npp h)
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh

lemma braid_inverse (h : a * b * a = b * a * b) :
    a⁻¹ * b⁻¹ * a⁻¹ = b⁻¹ * a⁻¹ * b⁻¹ := by
  have hh := congrArg (fun x : G => x⁻¹) h
  simpa only [mul_inv_rev, mul_assoc] using hh

/-- The crossing sign is determined by the fixed height order of the labels. -/
noncomputable def crossingSign (x y : ℝ) : ℤ := if x < y then 1 else -1

lemma crossingSign_swap {x y : ℝ} (hxy : x ≠ y) :
    crossingSign y x = -crossingSign x y := by
  by_cases h : x < y
  · have hn : ¬ y < x := not_lt_of_ge h.le
    simp [crossingSign, h, hn]
  · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt h) hxy.symm
    simp [crossingSign, h, hyx]

/-- The three-strand finite move holds for all realizable height-order signs.
The two cyclic sign patterns are impossible by transitivity of the real order. -/
theorem signed_braid_move (h : a * b * a = b * a * b) (x y z : ℝ) :
    a ^ crossingSign x y * b ^ crossingSign x z * a ^ crossingSign y z =
      b ^ crossingSign y z * a ^ crossingSign x z * b ^ crossingSign x y := by
  unfold crossingSign
  split_ifs <;> simp only [zpow_one, zpow_neg_one]
  · exact h
  · exact braid_mixed_ppn h
  · exfalso; linarith
  · exact braid_mixed_pnn h
  · exact braid_mixed_npp h
  · exfalso; linarith
  · exact braid_mixed_nnp h
  · exact braid_inverse h

/-- Reversing a crossing cancels it when the two heights are distinct. -/
theorem signed_backtrack (a : G) {x y : ℝ} (hxy : x ≠ y) :
    a ^ crossingSign x y * a ^ crossingSign y x = 1 := by
  rw [crossingSign_swap hxy, zpow_neg]
  exact mul_inv_cancel _

/-- Disjoint crossings commute with every pair of signs. -/
theorem signed_far_move (h : Commute a b) (x y u v : ℝ) :
    a ^ crossingSign x y * b ^ crossingSign u v =
      b ^ crossingSign u v * a ^ crossingSign x y :=
  (h.zpow_zpow (crossingSign x y) (crossingSign u v)).eq

end BraidConverse
end

/- WeightedConfluence -/
section
set_option autoImplicit false

namespace BraidConverse

open Relation

/-- Well-founded local confluence permits finite critical joins on both sides. -/
theorem wellFounded_confluence {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b))
    (hlocal : ∀ a b c, r a b → r a c → Join (ReflTransGen r) b c) :
    ∀ a b c, ReflTransGen r a b → ReflTransGen r a c → Join (ReflTransGen r) b c := by
  intro a
  induction a using hwf.induction with
  | h a ih =>
    intro b c hab hac
    rcases hab.cases_head with rfl | ⟨b₀, hab₀, hb₀b⟩
    · exact ⟨c, hac, .refl⟩
    rcases hac.cases_head with rfl | ⟨c₀, hac₀, hc₀c⟩
    · exact ⟨b, .refl, hab⟩
    obtain ⟨d, hb₀d, hc₀d⟩ := hlocal a b₀ c₀ hab₀ hac₀
    obtain ⟨e, hbe, hde⟩ := ih b₀ hab₀ b d hb₀b hb₀d
    obtain ⟨f, hcf, hef⟩ := ih c₀ hac₀ c e hc₀c (hc₀d.trans hde)
    exact ⟨f, hbe.trans hef, hcf⟩

theorem terminal_unique {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b))
    (hlocal : ∀ a b c, r a b → r a c → Join (ReflTransGen r) b c)
    {a b c : S} (hab : ReflTransGen r a b) (hac : ReflTransGen r a c)
    (hb : ∀ d, ¬ r b d) (hc : ∀ d, ¬ r c d) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := wellFounded_confluence r hwf hlocal a b c hab hac
  exact ((reflTransGen_iff_eq hb).mp hbd).symm.trans ((reflTransGen_iff_eq hc).mp hcd)

variable {S G : Type*} [Monoid G]

/-- A labelled rewrite accumulates its group or monoid value without erasing it. -/
def accumulatedStep (r : S → S → G → Prop) (a b : S × G) : Prop :=
  ∃ g, r a.1 b.1 g ∧ b.2 = a.2 * g

theorem accumulatedStep_wellFounded (r : S → S → G → Prop)
    (hwf : WellFounded (fun b a => ∃ g, r a b g)) :
    WellFounded (fun b a => accumulatedStep r a b) := by
  apply (InvImage.wf (Prod.fst : S × G → S) hwf).mono
  intro a b h
  obtain ⟨g, hg, _⟩ := h
  exact ⟨g, hg⟩

theorem terminal_accumulations_equal (r : S → S → G → Prop)
    (hwf : WellFounded (fun b a => ∃ g, r a b g))
    (hlocal : ∀ a b c, accumulatedStep r a b → accumulatedStep r a c →
      Join (ReflTransGen (accumulatedStep r)) b c)
    {a b c : S} {g₀ g₁ g₂ : G}
    (h₁ : ReflTransGen (accumulatedStep r) (a, g₀) (b, g₁))
    (h₂ : ReflTransGen (accumulatedStep r) (a, g₀) (c, g₂))
    (hb : ∀ d g, ¬ r b d g) (hc : ∀ d g, ¬ r c d g) : g₁ = g₂ := by
  have hb' : ∀ d, ¬ accumulatedStep r (b, g₁) d := by
    rintro d ⟨g, hg, _⟩
    exact hb d.1 g hg
  have hc' : ∀ d, ¬ accumulatedStep r (c, g₂) d := by
    rintro d ⟨g, hg, _⟩
    exact hc d.1 g hg
  exact congrArg Prod.snd (terminal_unique (accumulatedStep r)
    (accumulatedStep_wellFounded r hwf) hlocal h₁ h₂ hb' hc')

end BraidConverse
end

/- WeightedSortingConfluence -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Relation

namespace BraidConverse.PermutationSorting

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)

def afterStep (x : Permutation n × G) (i : Fin n) : Permutation n × G :=
  (swapAt x.1 i, (g i)⁻¹ * x.2)

lemma weighted_step (x : Permutation n × G) (i : Fin n) (hi : Descent x.1 i) :
    WeightedStep g x (afterStep g x i) := ⟨i, hi, rfl, rfl⟩

lemma weighted_far_join (x : Permutation n × G) (i j : Fin n)
    (hi : Descent x.1 i) (hj : Descent x.1 j)
    (hfar : i.val + 1 < j.val) (hcomm : Commute (g i) (g j)) :
    Join (ReflTransGen (WeightedStep g)) (afterStep g x i) (afterStep g x j) := by
  have hd := far_descent_preserved x.1 i j hfar
  have he : afterStep g (afterStep g x j) i = afterStep g (afterStep g x i) j := by
    apply Prod.ext
    · exact (swapAt_far_commute x.1 i j hfar).symm
    · change (g i)⁻¹ * ((g j)⁻¹ * x.2) = (g j)⁻¹ * ((g i)⁻¹ * x.2)
      simpa only [mul_assoc] using congrArg (fun v : G => v * x.2) hcomm.inv_inv.eq
  refine ⟨afterStep g (afterStep g x i) j, ?_, ?_⟩
  · exact ReflTransGen.single (weighted_step g (afterStep g x i) j (hd.2 hj))
  · rw [← he]
    exact ReflTransGen.single (weighted_step g (afterStep g x j) i (hd.1 hi))

lemma weighted_adjacent_join (x : Permutation n × G) (i j : Fin n)
    (hi : Descent x.1 i) (hj : Descent x.1 j)
    (hij : j.val = i.val + 1) (hbraid : g i * g j * g i = g j * g i * g j) :
    Join (ReflTransGen (WeightedStep g)) (afterStep g x i) (afterStep g x j) := by
  obtain ⟨hij1, hij2, hji1, hji2⟩ := adjacent_descent_diamond x.1 i j hij hi hj
  have he : afterStep g (afterStep g (afterStep g x j) i) j =
      afterStep g (afterStep g (afterStep g x i) j) i := by
    apply Prod.ext
    · exact (swapAt_braid x.1 i j hij).symm
    · change (g j)⁻¹ * ((g i)⁻¹ * ((g j)⁻¹ * x.2)) =
        (g i)⁻¹ * ((g j)⁻¹ * ((g i)⁻¹ * x.2))
      simpa only [mul_assoc] using
        congrArg (fun v : G => v * x.2) (BraidConverse.braid_inverse hbraid).symm
  refine ⟨afterStep g (afterStep g (afterStep g x i) j) i, ?_, ?_⟩
  · exact (ReflTransGen.single (weighted_step g (afterStep g x i) j hij1)).tail
      (weighted_step g (afterStep g (afterStep g x i) j) i hij2)
  · rw [← he]
    exact (ReflTransGen.single (weighted_step g (afterStep g x j) i hji1)).tail
      (weighted_step g (afterStep g (afterStep g x j) i) j hji2)

/-- The actual sorting critical pairs are precisely equality, disjoint
commuting descents, and the adjacent three-label braid diagram. -/
theorem weighted_local_confluence
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j) :
    ∀ x y z, WeightedStep g x y → WeightedStep g x z →
      Join (ReflTransGen (WeightedStep g)) y z := by
  intro x y z hy hz
  obtain ⟨i, hi, hy1, hy2⟩ := hy
  obtain ⟨j, hj, hz1, hz2⟩ := hz
  have hey : y = afterStep g x i := Prod.ext hy1 hy2
  have hez : z = afterStep g x j := Prod.ext hz1 hz2
  subst y
  subst z
  rcases lt_trichotomy i.val j.val with hij | hij | hji
  · by_cases hadj : j.val = i.val + 1
    · exact weighted_adjacent_join g x i j hi hj hadj (hbraid i j hadj)
    · have hsep : i.val + 1 < j.val := by omega
      exact weighted_far_join g x i j hi hj hsep (hfar i j hsep)
  · have he : i = j := Fin.ext hij
    subst j
    exact ⟨afterStep g x i, .refl, .refl⟩
  · by_cases hadj : i.val = j.val + 1
    · obtain ⟨w, hz, hy⟩ := weighted_adjacent_join g x j i hj hi hadj (hbraid j i hadj)
      exact ⟨w, hy, hz⟩
    · have hsep : j.val + 1 < i.val := by omega
      obtain ⟨w, hz, hy⟩ := weighted_far_join g x j i hj hi hsep (hfar j i hsep)
      exact ⟨w, hy, hz⟩

theorem weighted_confluence
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j) :
    ∀ x y z, ReflTransGen (WeightedStep g) x y → ReflTransGen (WeightedStep g) x z →
      Join (ReflTransGen (WeightedStep g)) y z :=
  BraidConverse.wellFounded_confluence (WeightedStep g) (weightedStep_wellFounded g)
    (weighted_local_confluence g hfar hbraid)

end BraidConverse.PermutationSorting
end

/- CanonicalReduction -/
section
set_option autoImplicit false

open Relation

namespace BraidConverse

theorem exists_terminal {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b)) :
    ∀ a, ∃ b, ReflTransGen r a b ∧ ∀ c, ¬ r b c := by
  classical
  intro a
  induction a using hwf.induction with
  | h a ih =>
    by_cases ht : ∀ b, ¬ r a b
    · exact ⟨a, .refl, ht⟩
    obtain ⟨b, hab⟩ := not_forall_not.mp ht
    obtain ⟨c, hbc, hc⟩ := ih b hab
    exact ⟨c, hbc.head hab, hc⟩

noncomputable def normalForm {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b)) (a : S) : S :=
  (exists_terminal r hwf a).choose

theorem normalForm_reachable {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b)) (a : S) :
    ReflTransGen r a (normalForm r hwf a) :=
  (exists_terminal r hwf a).choose_spec.1

theorem normalForm_terminal {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b)) (a : S) :
    ∀ b, ¬ r (normalForm r hwf a) b :=
  (exists_terminal r hwf a).choose_spec.2

theorem normalForm_step {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b))
    (hlocal : ∀ a b c, r a b → r a c → Join (ReflTransGen r) b c)
    {a b : S} (hab : r a b) : normalForm r hwf a = normalForm r hwf b :=
  terminal_unique r hwf hlocal (normalForm_reachable r hwf a)
    ((normalForm_reachable r hwf b).head hab)
    (normalForm_terminal r hwf a) (normalForm_terminal r hwf b)

theorem normalForm_eqvGen {S : Type*} (r : S → S → Prop)
    (hwf : WellFounded (fun b a => r a b))
    (hlocal : ∀ a b c, r a b → r a c → Join (ReflTransGen r) b c)
    {a b : S} (hab : EqvGen r a b) : normalForm r hwf a = normalForm r hwf b := by
  induction hab with
  | rel a b h => exact normalForm_step r hwf hlocal h
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Maps that preserve rewrite steps and terminal states commute with normalization. -/
theorem normalForm_map {S T : Type*} (r : S → S → Prop) (s : T → T → Prop)
    (hrwf : WellFounded (fun b a => r a b)) (hswf : WellFounded (fun b a => s a b))
    (hlocal : ∀ a b c, s a b → s a c → Join (ReflTransGen s) b c)
    (f : S → T) (hstep : ∀ a b, r a b → s (f a) (f b))
    (hterm : ∀ a, (∀ b, ¬ r a b) → ∀ c, ¬ s (f a) c) (a : S) :
    f (normalForm r hrwf a) = normalForm s hswf (f a) := by
  have hreach : ReflTransGen s (f a) (f (normalForm r hrwf a)) :=
    ReflTransGen.lift f hstep a _ (normalForm_reachable r hrwf a)
  exact terminal_unique s hswf hlocal hreach (normalForm_reachable s hswf (f a))
    (hterm _ (normalForm_terminal r hrwf a)) (normalForm_terminal s hswf (f a))

end BraidConverse
end

/- SortingTransport -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

namespace BraidConverse.PermutationSorting

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)

noncomputable def sortedState (p : Permutation n) (u : G) : Permutation n × G :=
  BraidConverse.normalForm (WeightedStep g) (weightedStep_wellFounded g) (p, u)

noncomputable def potential (p : Permutation n) : G := (sortedState g p 1).2

lemma weighted_terminal_iff (x : Permutation n × G) :
    (∀ y, ¬ WeightedStep g x y) ↔ x.1 = 1 := by
  constructor
  · intro h
    apply eq_one_of_no_descent
    intro i hi
    exact h (afterStep g x i) (weighted_step g x i hi)
  · intro h y hy
    obtain ⟨i, hi, _, _⟩ := hy
    unfold Descent at hi
    rw [h] at hi
    change i.succ < i.castSucc at hi
    have := hi
    simp only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc] at this
    omega

theorem sortedState_first (p : Permutation n) (u : G) :
    (sortedState g p u).1 = 1 :=
  (weighted_terminal_iff g _).mp
    (BraidConverse.normalForm_terminal (WeightedStep g) (weightedStep_wellFounded g) _)

variable
  (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
  (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)

include hfar hbraid

theorem sortedState_right_mul (p : Permutation n) (u v : G) :
    sortedState g p (u * v) =
      ((sortedState g p u).1, (sortedState g p u).2 * v) := by
  let f : Permutation n × G → Permutation n × G := fun x => (x.1, x.2 * v)
  have hstep : ∀ a b, WeightedStep g a b → WeightedStep g (f a) (f b) := by
    intro a b hab
    obtain ⟨i, hi, hp, hu⟩ := hab
    refine ⟨i, hi, hp, ?_⟩
    change b.2 * v = (g i)⁻¹ * (a.2 * v)
    rw [hu, mul_assoc]
  have hterm : ∀ a, (∀ b, ¬ WeightedStep g a b) → ∀ c, ¬ WeightedStep g (f a) c := by
    intro a ha
    apply (weighted_terminal_iff g (f a)).mpr
    exact (weighted_terminal_iff g a).mp ha
  exact (BraidConverse.normalForm_map (WeightedStep g) (WeightedStep g)
    (weightedStep_wellFounded g) (weightedStep_wellFounded g)
    (weighted_local_confluence g hfar hbraid) f hstep hterm (p, u)).symm

theorem sortedState_second (p : Permutation n) (u : G) :
    (sortedState g p u).2 = potential g p * u := by
  simpa only [one_mul, potential] using congrArg Prod.snd (sortedState_right_mul g hfar hbraid p 1 u)

theorem potential_one : potential g 1 = 1 := by
  have h := BraidConverse.terminal_unique (WeightedStep g) (weightedStep_wellFounded g)
    (weighted_local_confluence g hfar hbraid)
    (BraidConverse.normalForm_reachable (WeightedStep g) (weightedStep_wellFounded g) (1, 1))
    (Relation.ReflTransGen.refl : Relation.ReflTransGen (WeightedStep g) (1, 1) (1, 1))
    (BraidConverse.normalForm_terminal (WeightedStep g) (weightedStep_wellFounded g) (1, 1))
    ((weighted_terminal_iff g (1, 1)).mpr rfl)
  exact congrArg Prod.snd h

theorem potential_descent (p : Permutation n) (i : Fin n) (hi : Descent p i) :
    potential g p = potential g (swapAt p i) * (g i)⁻¹ := by
  have h := BraidConverse.normalForm_step (WeightedStep g) (weightedStep_wellFounded g)
    (weighted_local_confluence g hfar hbraid) (weighted_step g (p, 1) i hi)
  have hs := congrArg Prod.snd h
  change potential g p = (sortedState g (swapAt p i) ((g i)⁻¹ * 1)).2 at hs
  simpa only [mul_one, sortedState_second g hfar hbraid] using hs

omit hfar hbraid in
lemma swapAt_twice (p : Permutation n) (i : Fin n) : swapAt (swapAt p i) i = p := by
  apply Equiv.ext
  intro k
  simp only [swapAt_apply, Equiv.swap_apply_self]

omit hfar hbraid in
lemma descent_after_ascent (p : Permutation n) (i : Fin n) (hi : ¬ Descent p i) :
    Descent (swapAt p i) i := by
  change swapAt p i i.succ < swapAt p i i.castSucc
  rw [swapAt_right, swapAt_left]
  have hn : p i.castSucc ≠ p i.succ := by
    intro he
    have hh := p.injective he
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  exact lt_of_le_of_ne (le_of_not_gt hi) hn

def crossingWeight (p : Permutation n) (i : Fin n) : G :=
  if p i.succ < p i.castSucc then (g i)⁻¹ else g i

/-- Every signed adjacent crossing is a difference of the same permutation potential. -/
theorem crossingWeight_eq_potential (p : Permutation n) (i : Fin n) :
    crossingWeight g p i = (potential g (swapAt p i))⁻¹ * potential g p := by
  classical
  by_cases hi : Descent p i
  · rw [crossingWeight, if_pos (show p i.succ < p i.castSucc from hi),
      potential_descent g hfar hbraid p i hi]
    simp only [inv_mul_cancel_left]
  · have h := potential_descent g hfar hbraid (swapAt p i) i (descent_after_ascent p i hi)
    rw [swapAt_twice] at h
    rw [crossingWeight, if_neg (show ¬ p i.succ < p i.castSucc from hi), h]
    group

noncomputable def transport (p q : Permutation n) : G := (potential g q)⁻¹ * potential g p

omit hfar hbraid in
theorem transport_trans (p q r : Permutation n) :
    transport g q r * transport g p q = transport g p r := by
  unfold transport
  group

omit hfar hbraid in
theorem transport_self (p : Permutation n) : transport g p p = 1 := by
  exact inv_mul_cancel (potential g p)

end BraidConverse.PermutationSorting
end

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

/- ComparisonCells -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set
open BraidNormalForm

noncomputable section

namespace BraidConverse

def imagGap {n : ℕ} (p : StrandPair n) : (Fin n → ℂ) →L[ℝ] ℝ where
  toFun z := (z p.val.1).im - (z p.val.2).im
  map_add' := by intro x y; simp only [Pi.add_apply, Complex.add_im]; ring
  map_smul' := by intro c x; simp; ring
  cont := by fun_prop

def comparisonForm {n : ℕ} (z : configurations n) (p : StrandPair n) :
    (Fin n → ℂ) →L[ℝ] ℝ := by
  classical
  exact if realGap p z.val = 0 then (imagGap p z.val) • imagGap p
    else (realGap p z.val) • realGap p

def comparisonCell {n : ℕ} (z : configurations n) : Set (Fin n → ℂ) :=
  {w | ∀ p : StrandPair n, 0 < comparisonForm z p w}

theorem comparisonForm_self_pos {n : ℕ} (z : configurations n) (p : StrandPair n) :
    0 < comparisonForm z p z.val := by
  classical
  by_cases hr : realGap p z.val = 0
  · have hi : imagGap p z.val ≠ 0 := by
      intro him
      apply ne_of_lt p.property
      apply z.property
      apply Complex.ext
      · exact sub_eq_zero.mp hr
      · exact sub_eq_zero.mp him
    simpa only [comparisonForm, hr, ↓reduceIte, smul_apply, smul_eq_mul]
      using mul_self_pos.mpr hi
  · simpa only [comparisonForm, hr, ↓reduceIte, smul_apply, smul_eq_mul]
      using mul_self_pos.mpr hr

theorem comparisonCell_self {n : ℕ} (z : configurations n) : z.val ∈ comparisonCell z :=
  comparisonForm_self_pos z

theorem comparisonCell_open {n : ℕ} (z : configurations n) : IsOpen (comparisonCell z) := by
  have he : comparisonCell z = ⋂ p : StrandPair n, {w | 0 < comparisonForm z p w} := by
    ext w
    simp only [comparisonCell, mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite fun p => isOpen_lt continuous_const (comparisonForm z p).continuous

theorem comparisonCell_convex {n : ℕ} (z : configurations n) :
    Convex ℝ (comparisonCell z) := by
  intro x hx y hy a b ha hb hab p
  change 0 < comparisonForm z p (a • x + b • y)
  simp only [map_add, map_smul, smul_eq_mul]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hy p
  · have hpos := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) (hx p)
    have hnonneg := mul_nonneg hb (hy p).le
    linarith

theorem comparisonForm_zero_of_collision {n : ℕ} (z : configurations n) (p : StrandPair n)
    (w : Fin n → ℂ) (hw : w p.val.1 = w p.val.2) : comparisonForm z p w = 0 := by
  have hr : realGap p w = 0 := sub_eq_zero.mpr (congrArg Complex.re hw)
  have hi : imagGap p w = 0 := sub_eq_zero.mpr (congrArg Complex.im hw)
  unfold comparisonForm
  split_ifs <;> simp only [smul_apply, smul_eq_mul, hr, hi, mul_zero]

theorem comparisonCell_subset_configurations {n : ℕ} (z : configurations n) :
    comparisonCell z ⊆ configurations n := by
  intro w hw i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hw ⟨(i, j), hlt⟩
    rw [comparisonForm_zero_of_collision z ⟨(i, j), hlt⟩ w hij] at h
    exact (lt_irrefl 0) h
  · have h := hw ⟨(j, i), hgt⟩
    rw [comparisonForm_zero_of_collision z ⟨(j, i), hgt⟩ w hij.symm] at h
    exact (lt_irrefl 0) h

theorem comparisonCell_pair_order {n : ℕ} (z : configurations n) (p : StrandPair n) :
    (∀ w ∈ comparisonCell z, 0 < realGap p z.val * realGap p w) ∨
      (∀ w ∈ comparisonCell z, 0 < imagGap p z.val * imagGap p w) := by
  classical
  by_cases hr : realGap p z.val = 0
  · right
    intro w hw
    simpa only [comparisonForm, hr, ↓reduceIte, smul_apply, smul_eq_mul]
      using hw p
  · left
    intro w hw
    simpa only [comparisonForm, hr, ↓reduceIte, smul_apply, smul_eq_mul]
      using hw p

end BraidConverse

end
end

/- ComparisonCellRanks -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set BraidNormalForm

noncomputable section

namespace BraidConverse

theorem exists_sorted_permutation {n : ℕ} {α : Type*} [LinearOrder α]
    (f : Fin n → α) (hf : Function.Injective f) :
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

def centerValue {n : ℕ} (z : configurations n) (i : Fin n) : ℝ ×ₗ ℝ :=
  toLex ((z.val i).re, (z.val i).im)

theorem centerValue_injective {n : ℕ} (z : configurations n) :
    Function.Injective (centerValue z) := by
  intro i j hij
  apply z.property
  apply Complex.ext
  · exact congrArg (fun v : ℝ ×ₗ ℝ => (ofLex v).1) hij
  · exact congrArg (fun v : ℝ ×ₗ ℝ => (ofLex v).2) hij

/-- Rank labels by the center's lexicographic real/imaginary order. -/
def centerRank {n : ℕ} (z : configurations n) : Equiv.Perm (Fin n) :=
  (exists_sorted_permutation (centerValue z) (centerValue_injective z)).choose.symm

theorem centerRank_lt_iff {n : ℕ} (z : configurations n) (i j : Fin n) :
    centerRank z i < centerRank z j ↔
      (z.val i).re < (z.val j).re ∨
        (z.val i).re = (z.val j).re ∧ (z.val i).im < (z.val j).im := by
  have hm := (exists_sorted_permutation (centerValue z) (centerValue_injective z)).choose_spec
  have he := hm.lt_iff_lt (a := centerRank z i) (b := centerRank z j)
  simpa only [centerRank, Equiv.apply_symm_apply, centerValue,
    Prod.Lex.toLex_lt_toLex] using he.symm

theorem comparisonCell_pair_product {n : ℕ} (z : configurations n)
    {w : Fin n → ℂ} (hw : w ∈ comparisonCell z) (i j : Fin n) (hij : i ≠ j) :
    if (z.val i).re = (z.val j).re then
      0 < ((z.val i).im - (z.val j).im) * ((w i).im - (w j).im)
    else 0 < ((z.val i).re - (z.val j).re) * ((w i).re - (w j).re) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := hw ⟨(i, j), hlt⟩
    unfold comparisonForm at h
    by_cases he : (z.val i).re = (z.val j).re
    · have hr : realGap ⟨(i, j), hlt⟩ z.val = 0 := sub_eq_zero.mpr he
      rw [if_pos hr] at h
      change 0 < ((z.val i).im - (z.val j).im) * ((w i).im - (w j).im) at h
      simpa only [if_pos he] using h
    · have hr : realGap ⟨(i, j), hlt⟩ z.val ≠ 0 := sub_ne_zero.mpr he
      rw [if_neg hr] at h
      change 0 < ((z.val i).re - (z.val j).re) * ((w i).re - (w j).re) at h
      simpa only [if_neg he] using h
  · have h := hw ⟨(j, i), hgt⟩
    unfold comparisonForm at h
    by_cases he : (z.val i).re = (z.val j).re
    · have hr : realGap ⟨(j, i), hgt⟩ z.val = 0 := sub_eq_zero.mpr he.symm
      rw [if_pos hr] at h
      change 0 < ((z.val j).im - (z.val i).im) * ((w j).im - (w i).im) at h
      rw [if_pos he]
      nlinarith
    · have hr : realGap ⟨(j, i), hgt⟩ z.val ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
      rw [if_neg hr] at h
      change 0 < ((z.val j).re - (z.val i).re) * ((w j).re - (w i).re) at h
      rw [if_neg he]
      nlinarith

theorem comparisonCell_real_order {n : ℕ} (z : configurations n)
    {w : Fin n → ℂ} (hw : w ∈ comparisonCell z) {i j : Fin n}
    (hij : (z.val i).re < (z.val j).re) : (w i).re < (w j).re := by
  have hne : i ≠ j := by rintro rfl; exact (lt_irrefl _) hij
  have h := comparisonCell_pair_product z hw i j hne
  rw [if_neg (ne_of_lt hij)] at h
  nlinarith

theorem comparisonCell_imag_order {n : ℕ} (z : configurations n)
    {w : Fin n → ℂ} (hw : w ∈ comparisonCell z) {i j : Fin n}
    (hre : (z.val i).re = (z.val j).re) :
    (w i).im < (w j).im ↔ centerRank z i < centerRank z j := by
  by_cases hij : i = j
  · subst j
    simp only [lt_self_iff_false]
  have h := comparisonCell_pair_product z hw i j hij
  rw [if_pos hre] at h
  rw [centerRank_lt_iff]
  simp only [hre, lt_self_iff_false, true_and, false_or]
  constructor <;> intro hlt <;> nlinarith

/-- Any real-coordinate coincidence inside the cell belongs to one equal-real
cluster of its center, where the fixed imaginary order determines the sign. -/
theorem comparisonCell_crossing_rank {n : ℕ} (z : configurations n)
    {w : Fin n → ℂ} (hw : w ∈ comparisonCell z) {i j : Fin n}
    (he : (w i).re = (w j).re) :
    (z.val i).re = (z.val j).re ∧
      ((w i).im < (w j).im ↔ centerRank z i < centerRank z j) := by
  have hre : (z.val i).re = (z.val j).re := by
    rcases lt_trichotomy (z.val i).re (z.val j).re with hlt | heq | hgt
    · have h := comparisonCell_real_order z hw hlt
      exact False.elim ((ne_of_lt h) he)
    · exact heq
    · have h := comparisonCell_real_order z hw hgt
      exact False.elim ((ne_of_lt h) he.symm)
  exact ⟨hre, comparisonCell_imag_order z hw hre⟩

end BraidConverse

end
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

/- RankedRealOrder -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set unitInterval BraidsLinksMCG BraidNormalForm

noncomputable section

namespace BraidConverse

def rankedRealOrder {n : ℕ} (z a : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re)) :
    PermutationSorting.Permutation n := centerRank z * sortingPermutation a ha

theorem sortingPermutation_eq_of_chamber {n : ℕ} (a : OrderedConfig n)
    (ha : Function.Injective (fun k => (a.val k).re)) (perm : Equiv.Perm (Fin n))
    (hperm : a.val ∈ realChamber perm) : sortingPermutation a ha = perm :=
  sorting_permutation_unique (fun k => (a.val k).re) (sortingPermutation_strictMono a ha) hperm

theorem rankedRealOrder_no_crossing {n : ℕ} (z : OrderedConfig (n + 1))
    {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hreal : ∀ t : I, Function.Injective (fun k => ((p t).val k).re)) :
    rankedRealOrder z b hb = rankedRealOrder z a ha := by
  have hch := no_crossing_path_in_chamber (sortingPermutation a ha) p
    (sortingPermutation_strictMono a ha) hreal 1
  have he := sortingPermutation_eq_of_chamber b hb (sortingPermutation a ha)
    (by simpa only [p.target] using hch)
  simp only [rankedRealOrder, he]

theorem adjacent_eq_canonical {n : ℕ} (i : Fin n) :
    PermutationSorting.adjacent n i = adjacentSwap (n := n + 1) i := by
  rfl

theorem rankedRealOrder_after_swap {n : ℕ} (z : OrderedConfig (n + 1))
    {a b : OrderedConfig (n + 1)}
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) (i : Fin n)
    (hch : b.val ∈ realChamber (sortingPermutation a ha * PermutationSorting.adjacent n i)) :
    rankedRealOrder z b hb = PermutationSorting.swapAt (rankedRealOrder z a ha) i := by
  have he := sortingPermutation_eq_of_chamber b hb _ hch
  simp only [rankedRealOrder, he, PermutationSorting.swapAt, mul_assoc]

/-- The crossing sign in a comparison cell is the ascent/descent sign of the
ranked real-order permutation. -/
theorem rankedRealOrder_crossing_sign {n : ℕ} (z a : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re)) (i : Fin n)
    {w : Fin (n + 1) → ℂ} (hw : w ∈ comparisonCell z)
    (he : (w (sortingPermutation a ha i.castSucc)).re =
      (w (sortingPermutation a ha i.succ)).re) :
    (0 < (w (sortingPermutation a ha i.succ)).im -
      (w (sortingPermutation a ha i.castSucc)).im ↔
      rankedRealOrder z a ha i.castSucc < rankedRealOrder z a ha i.succ) ∧
    ((w (sortingPermutation a ha i.succ)).im -
      (w (sortingPermutation a ha i.castSucc)).im < 0 ↔
      PermutationSorting.Descent (rankedRealOrder z a ha) i) := by
  have h := comparisonCell_crossing_rank z hw he
  have hrev := comparisonCell_crossing_rank z hw he.symm
  constructor
  · simpa only [sub_pos, rankedRealOrder, Equiv.Perm.coe_mul, Function.comp_apply] using h.2
  · simpa only [sub_neg, rankedRealOrder, Equiv.Perm.coe_mul, Function.comp_apply,
      PermutationSorting.Descent] using hrev.2

end BraidConverse

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

/- CellWordInterface -/
section
set_option autoImplicit false

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G]

def letterValue (g : Fin n → G) (a : BraidLetter (n + 1)) : G :=
  match a.sign with
  | .positive => g a.index
  | .negative => (g a.index)⁻¹

def wordValue (g : Fin n → G) : List (BraidLetter (n + 1)) → G
  | [] => 1
  | a :: w => letterValue g a * wordValue g w

theorem wordValue_append (g : Fin n → G) (v w : List (BraidLetter (n + 1))) :
    wordValue g (v ++ w) = wordValue g v * wordValue g w := by
  induction v with
  | nil => simp only [List.nil_append, wordValue, one_mul]
  | cons a v ih => simp only [List.cons_append, wordValue, ih, mul_assoc]

noncomputable def cellTransport (g : Fin n → G) (z a b : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) : G :=
  PermutationSorting.transport g (rankedRealOrder z a ha) (rankedRealOrder z b hb)

/-- A single word describes the edge geometrically and has the correct algebraic
value in every comparison cell containing it. Shared grid edges therefore use
the same word in both incident cells. -/
def CellTraceHasWord (g : Fin n → G) {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) : Prop :=
  ∃ w : List (BraidLetter (n + 1)),
    (basedTrace (canonicalChamberApproach a ha) (p.map (configProj (n + 1)).continuous)
      (canonicalChamberApproach b hb)).Homotopic (braidWordLoop (n + 1) w) ∧
    ∀ z : OrderedConfig (n + 1), (∀ t : I, (p t).val ∈ comparisonCell z) →
      wordValue g w = cellTransport g z a b ha hb

end BraidConverse
end

/- GroupGridCancellation -/
section
set_option autoImplicit false

namespace BraidConverse

variable {G : Type*} [Group G]

/-- Later oriented edges multiply on the left, as in the path convention. -/
def edgeProduct (f : ℕ → G) : ℕ → G
  | 0 => 1
  | k + 1 => f k * edgeProduct f k

lemma strip_transport (H V : ℕ → ℕ → G) (m j : ℕ)
    (hc : ∀ i < m, V (i + 1) j * H i j = H i (j + 1) * V i j) :
    V m j * edgeProduct (fun i => H i j) m =
      edgeProduct (fun i => H i (j + 1)) m * V 0 j := by
  induction m with
  | zero => simp only [edgeProduct, mul_one, one_mul]
  | succ m ih =>
    have hm := hc m (Nat.lt_succ_self m)
    have hp := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    change V (m + 1) j * (H m j * edgeProduct (fun i => H i j) m) =
      (H m (j + 1) * edgeProduct (fun i => H i (j + 1)) m) * V 0 j
    rw [← mul_assoc, hm, mul_assoc, hp, ← mul_assoc]

/-- Equality around each elementary square gives equality around the grid. -/
theorem rectangular_grid_transport (H V : ℕ → ℕ → G) (m k : ℕ)
    (hc : ∀ i < m, ∀ j < k,
      V (i + 1) j * H i j = H i (j + 1) * V i j) :
    edgeProduct (V m) k * edgeProduct (fun i => H i 0) m =
      edgeProduct (fun i => H i k) m * edgeProduct (V 0) k := by
  induction k with
  | zero => simp only [edgeProduct, one_mul, mul_one]
  | succ k ih =>
    have hp := ih (fun i hi j hj => hc i hi j (Nat.lt_succ_of_lt hj))
    have hs := strip_transport H V m k (fun i hi => hc i hi k (Nat.lt_succ_self k))
    change (V m k * edgeProduct (V m) k) * edgeProduct (fun i => H i 0) m =
      edgeProduct (fun i => H i (k + 1)) m * (V 0 k * edgeProduct (V 0) k)
    rw [mul_assoc, hp, ← mul_assoc, hs, mul_assoc]

theorem rectangular_boundary_eq_one (H V : ℕ → ℕ → G) (m k : ℕ)
    (hc : ∀ i < m, ∀ j < k,
      V (i + 1) j * H i j = H i (j + 1) * V i j) :
    (edgeProduct (fun i => H i k) m)⁻¹ * edgeProduct (V m) k *
      edgeProduct (fun i => H i 0) m * (edgeProduct (V 0) k)⁻¹ = 1 := by
  have h := rectangular_grid_transport H V m k hc
  rw [mul_assoc ((edgeProduct (fun i => H i k) m)⁻¹), h]
  group

lemma edgeProduct_eq_one (f : ℕ → G) (k : ℕ) (hf : ∀ j < k, f j = 1) :
    edgeProduct f k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change f k * edgeProduct f k = 1
    rw [hf k (Nat.lt_succ_self k), ih (fun j hj => hf j (Nat.lt_succ_of_lt hj)), one_mul]

theorem grid_bottom_eq_one (H V : ℕ → ℕ → G) (m k : ℕ)
    (hc : ∀ i < m, ∀ j < k,
      V (i + 1) j * H i j = H i (j + 1) * V i j)
    (hleft : ∀ j < k, V 0 j = 1) (hright : ∀ j < k, V m j = 1)
    (htop : ∀ i < m, H i k = 1) :
    edgeProduct (fun i => H i 0) m = 1 := by
  have h := rectangular_grid_transport H V m k hc
  simpa only [edgeProduct_eq_one _ _ hleft, edgeProduct_eq_one _ _ hright,
    edgeProduct_eq_one _ _ htop, one_mul, mul_one] using h

end BraidConverse
end

/- PartialWordValue -/
section
set_option autoImplicit false

open TarchaBraids

noncomputable section

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)

def referencePartialValue (a : BraidLetter (n + 1)) (t : ℝ) : G :=
  if t ≤ 1 / 2 then 1 else letterValue g a

def partialWordValue : List (BraidLetter (n + 1)) → ℝ → G
  | [], _ => 1
  | a :: w, t => if t ≤ 1 / 2 then partialWordValue w (2 * t)
      else referencePartialValue g a (2 * t - 1) * wordValue g w

theorem partialWordValue_zero (w : List (BraidLetter (n + 1))) :
    partialWordValue g w 0 = 1 := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [partialWordValue, show (0 : ℝ) ≤ 1 / 2 by norm_num,
      if_true, mul_zero] using ih

theorem partialWordValue_after_last (w : List (BraidLetter (n + 1)))
    (t : ℝ) (ht : 3 / 4 < t) : partialWordValue g w t = wordValue g w := by
  cases w with
  | nil => rfl
  | cons a w =>
    have hhalf : ¬ t ≤ 1 / 2 := by linarith
    have hlocal : ¬ 2 * t - 1 ≤ 1 / 2 := by linarith
    simp only [partialWordValue, if_neg hhalf, referencePartialValue, if_neg hlocal, wordValue]

theorem partialWordValue_one (w : List (BraidLetter (n + 1))) :
    partialWordValue g w 1 = wordValue g w :=
  partialWordValue_after_last g w 1 (by norm_num)

theorem partialWordValue_cons_left (a : BraidLetter (n + 1)) (w : List (BraidLetter (n + 1)))
    (t : ℝ) (ht : t ≤ 1 / 2) :
    partialWordValue g (a :: w) t = partialWordValue g w (2 * t) := by
  exact if_pos ht

theorem partialWordValue_cons_right (a : BraidLetter (n + 1)) (w : List (BraidLetter (n + 1)))
    (t : ℝ) (ht : 1 / 2 ≤ t) :
    partialWordValue g (a :: w) t = referencePartialValue g a (2 * t - 1) * wordValue g w := by
  by_cases h : t ≤ 1 / 2
  · have he : t = 1 / 2 := le_antisymm h ht
    subst t
    rw [partialWordValue_cons_left g a w _ le_rfl]
    have he : 2 * (1 / 2 : ℝ) = 1 := by ring
    rw [he, partialWordValue_one]
    norm_num [referencePartialValue]
  · exact if_neg h

theorem referencePartialValue_ratio (a : BraidLetter (n + 1)) (u v : ℝ)
    (hu : u ≠ 1 / 2) (_hv : v ≠ 1 / 2) (huv : u ≤ v) :
    referencePartialValue g a v * (referencePartialValue g a u)⁻¹ =
      if u < 1 / 2 ∧ 1 / 2 < v then letterValue g a else 1 := by
  by_cases hul : u ≤ 1 / 2
  · by_cases hvl : v ≤ 1 / 2
    · simp only [referencePartialValue, if_pos hul, if_pos hvl, inv_one, mul_one,
        if_neg (fun h : u < (1 / 2 : ℝ) ∧ 1 / 2 < v => (not_lt_of_ge hvl) h.2)]
    · have hug : u < 1 / 2 := lt_of_le_of_ne hul hu
      have hvg : 1 / 2 < v := lt_of_not_ge hvl
      simp only [referencePartialValue, if_pos hul, if_neg hvl, inv_one, mul_one,
        if_pos (show u < (1 / 2 : ℝ) ∧ 1 / 2 < v from ⟨hug, hvg⟩)]
  · have hvl : ¬ v ≤ 1 / 2 := fun h => hul (huv.trans h)
    simp only [referencePartialValue, if_neg hul, if_neg hvl, mul_inv_cancel,
      if_neg (fun h : u < (1 / 2 : ℝ) ∧ 1 / 2 < v => hul h.1.le)]

def wordMesh (w : List (BraidLetter (n + 1))) : ℝ := 1 / (8 * 2 ^ w.length)

theorem wordMesh_pos (w : List (BraidLetter (n + 1))) : 0 < wordMesh w := by
  unfold wordMesh
  positivity

theorem wordMesh_cons (a : BraidLetter (n + 1)) (w : List (BraidLetter (n + 1))) :
    2 * wordMesh (a :: w) = wordMesh w := by
  unfold wordMesh
  rw [List.length_cons, pow_succ]
  ring

theorem wordMesh_le (w : List (BraidLetter (n + 1))) : wordMesh w ≤ 1 / 8 := by
  unfold wordMesh
  have hpow : (1 : ℝ) ≤ 2 ^ w.length := one_le_pow₀ (by norm_num)
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8)
  nlinarith

theorem edgeProduct_potential (P : ℕ → G) (m : ℕ) :
    edgeProduct (fun i => P (i + 1) * (P i)⁻¹) m = P m * (P 0)⁻¹ := by
  induction m with
  | zero => simp only [edgeProduct, mul_inv_cancel]
  | succ m ih => rw [edgeProduct, ih]; group

theorem edgeProduct_congr (f h : ℕ → G) (m : ℕ) (he : ∀ i < m, f i = h i) :
    edgeProduct f m = edgeProduct h m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [edgeProduct, edgeProduct, he m (Nat.lt_succ_self m),
      ih (fun i hi => he i (Nat.lt_succ_of_lt hi))]

end BraidConverse

end
end

/- CellTransportRelabel -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set BraidsLinksMCG BraidNormalForm

namespace BraidConverse

theorem permutation_eq_of_order_iff {n : ℕ} (p q : Equiv.Perm (Fin n))
    (h : ∀ i j, p i < p j ↔ q i < q j) : p = q := by
  have hm : StrictMono (fun k => q (p.symm k)) := by
    intro i j hij
    apply (h _ _).mp
    simpa only [Equiv.apply_symm_apply] using hij
  apply Equiv.ext
  intro i
  have he := hm.apply_eq (x := p i)
  simpa only [Equiv.symm_apply_apply] using he.symm

theorem centerRank_relabel {n : ℕ} (perm : Equiv.Perm (Fin n)) (z : OrderedConfig n) :
    centerRank (relabelConfig perm z) = centerRank z * perm := by
  apply permutation_eq_of_order_iff
  intro i j
  change centerRank (relabelConfig perm z) i < centerRank (relabelConfig perm z) j ↔
    centerRank z (perm i) < centerRank z (perm j)
  exact (centerRank_lt_iff (relabelConfig perm z) i j).trans
    (centerRank_lt_iff z (perm i) (perm j)).symm

theorem comparisonCell_relabel {n : ℕ} (perm : Equiv.Perm (Fin n)) (z : OrderedConfig n)
    {w : Fin n → ℂ} (hw : w ∈ comparisonCell z) :
    w ∘ perm ∈ comparisonCell (relabelConfig perm z) := by
  intro p
  have hij : perm p.val.1 ≠ perm p.val.2 :=
    fun he => (ne_of_lt p.property) (perm.injective he)
  have h := comparisonCell_pair_product z hw (perm p.val.1) (perm p.val.2) hij
  unfold comparisonForm
  by_cases he : (z.val (perm p.val.1)).re = (z.val (perm p.val.2)).re
  · have hr : realGap p (relabelConfig perm z).val = 0 := sub_eq_zero.mpr he
    rw [if_pos hr]
    change 0 < ((z.val (perm p.val.1)).im - (z.val (perm p.val.2)).im) *
      ((w (perm p.val.1)).im - (w (perm p.val.2)).im)
    simpa only [if_pos he] using h
  · have hr : realGap p (relabelConfig perm z).val ≠ 0 := sub_ne_zero.mpr he
    rw [if_neg hr]
    change 0 < ((z.val (perm p.val.1)).re - (z.val (perm p.val.2)).re) *
      ((w (perm p.val.1)).re - (w (perm p.val.2)).re)
    simpa only [if_neg he] using h

theorem rankedRealOrder_relabel {n : ℕ} (perm : Equiv.Perm (Fin (n + 1)))
    (z a : OrderedConfig (n + 1)) (ha : Function.Injective (fun k => (a.val k).re)) :
    rankedRealOrder (relabelConfig perm z) (relabelConfig perm a)
      (relabel_real_injective perm a ha) = rankedRealOrder z a ha := by
  change centerRank (relabelConfig perm z) *
    sortingPermutation (relabelConfig perm a) (relabel_real_injective perm a ha) =
      centerRank z * sortingPermutation a ha
  calc
    _ = (centerRank z * perm) * ((sortingPermutation a ha).trans perm.symm) :=
      congrArg₂ (fun p q : Equiv.Perm (Fin (n + 1)) => p * q)
        (centerRank_relabel perm z) (sortingPermutation_relabel perm a ha)
    _ = centerRank z * sortingPermutation a ha := by
      change (centerRank z * perm) * (perm⁻¹ * sortingPermutation a ha) = _
      group

theorem cellTransport_relabel {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (perm : Equiv.Perm (Fin (n + 1))) (z a b : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) :
    cellTransport g (relabelConfig perm z) (relabelConfig perm a) (relabelConfig perm b)
      (relabel_real_injective perm a ha) (relabel_real_injective perm b hb) =
    cellTransport g z a b ha hb := by
  unfold cellTransport
  rw [rankedRealOrder_relabel, rankedRealOrder_relabel]

end BraidConverse
end

/- CrossingCellValue -/
section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set BraidsLinksMCG BraidNormalForm

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
  (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
  (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)

include hfar hbraid

/-- The value of a positive crossing requires only the endpoint chamber swap
and one actual signed crossing in the comparison cell. No affine path premise. -/
theorem positive_crossing_cell_value (z a b : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) (i : Fin n)
    (hbch : b.val ∈ realChamber (sortingPermutation a ha * PermutationSorting.adjacent n i))
    {w : Fin (n + 1) → ℂ} (hw : w ∈ comparisonCell z)
    (he : (w (sortingPermutation a ha i.castSucc)).re =
      (w (sortingPermutation a ha i.succ)).re)
    (hpos : 0 < (w (sortingPermutation a ha i.succ)).im -
      (w (sortingPermutation a ha i.castSucc)).im) :
    cellTransport g z a b ha hb = g i := by
  have hsg := (rankedRealOrder_crossing_sign z a ha i hw he).1.mp hpos
  have hnd : ¬ (rankedRealOrder z a ha i.succ < rankedRealOrder z a ha i.castSucc) :=
    not_lt_of_ge hsg.le
  have hafter := rankedRealOrder_after_swap z ha hb i hbch
  unfold cellTransport PermutationSorting.transport
  rw [hafter, ← PermutationSorting.crossingWeight_eq_potential g hfar hbraid]
  exact if_neg hnd

theorem negative_crossing_cell_value (z a b : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) (i : Fin n)
    (hbch : b.val ∈ realChamber (sortingPermutation a ha * PermutationSorting.adjacent n i))
    {w : Fin (n + 1) → ℂ} (hw : w ∈ comparisonCell z)
    (he : (w (sortingPermutation a ha i.castSucc)).re =
      (w (sortingPermutation a ha i.succ)).re)
    (hneg : (w (sortingPermutation a ha i.succ)).im -
      (w (sortingPermutation a ha i.castSucc)).im < 0) :
    cellTransport g z a b ha hb = (g i)⁻¹ := by
  have hsg := (rankedRealOrder_crossing_sign z a ha i hw he).2.mp hneg
  have hafter := rankedRealOrder_after_swap z ha hb i hbch
  unfold cellTransport PermutationSorting.transport
  rw [hafter, ← PermutationSorting.crossingWeight_eq_potential g hfar hbraid]
  exact if_pos hsg

end BraidConverse
end

/- ReferenceSliceValue -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)

theorem cellTransport_eq_one_of_chamber (z a b : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (order : Equiv.Perm (Fin (n + 1)))
    (ham : a.val ∈ realChamber order) (hbm : b.val ∈ realChamber order) :
    cellTransport g z a b ha hb = 1 := by
  unfold cellTransport rankedRealOrder
  rw [sortingPermutation_eq_of_chamber a ha order ham,
    sortingPermutation_eq_of_chamber b hb order hbm]
  exact PermutationSorting.transport_self g _

/-- A reference-letter interval contributes its signed generator exactly when
it contains the sole midpoint crossing; every other interval contributes one. -/
theorem reference_slice_value
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    (z : OrderedConfig (n + 1)) (i : Fin n) (s : BraidLetterSign) (u v : I)
    (hu : (u : ℝ) ≠ 1 / 2) (hv : (v : ℝ) ≠ 1 / 2) (huv : u ≤ v)
    (hcell : ∀ t : I, u ≤ t → t ≤ v → (signedReference n i s t).val ∈ comparisonCell z) :
    cellTransport g z (signedReference n i s u) (signedReference n i s v)
      (signedReference_real_injective n i s u hu) (signedReference_real_injective n i s v hv) =
      if (u : ℝ) < 1 / 2 ∧ 1 / 2 < (v : ℝ) then letterValue g ⟨i, s⟩ else 1 := by
  let a := signedReference n i s u
  let b := signedReference n i s v
  have ha := signedReference_real_injective n i s u hu
  have hb := signedReference_real_injective n i s v hv
  by_cases hul : (u : ℝ) < 1 / 2
  · by_cases hvl : (v : ℝ) < 1 / 2
    · rw [if_neg (fun h => (not_lt_of_ge hvl.le) h.2)]
      exact cellTransport_eq_one_of_chamber g z a b ha hb _
        (signedReference_before n i s u hul) (signedReference_before n i s v hvl)
    · have hvg : 1 / 2 < (v : ℝ) := lt_of_le_of_ne (le_of_not_gt hvl) hv.symm
      rw [if_pos ⟨hul, hvg⟩]
      have hsort : sortingPermutation a ha = Equiv.refl (Fin (n + 1)) :=
        sortingPermutation_eq_of_chamber a ha _ (signedReference_before n i s u hul)
      have hbch : b.val ∈ realChamber (sortingPermutation a ha * PermutationSorting.adjacent n i) := by
        rw [hsort]
        exact signedReference_after n i s v hvg
      have hm : (signedReference n i s halfTime).val ∈ comparisonCell z :=
        hcell halfTime hul.le hvg.le
      have he : ((signedReference n i s halfTime).val (sortingPermutation a ha i.castSucc)).re =
          ((signedReference n i s halfTime).val (sortingPermutation a ha i.succ)).re := by
        rw [hsort]
        exact signedReference_mid_pair n i s
      have h0 : halfTime ≠ 0 := by
        intro h
        have hh := congrArg Subtype.val h
        norm_num [halfTime] at hh
      have h1 : halfTime ≠ 1 := by
        intro h
        have hh := congrArg Subtype.val h
        norm_num [halfTime] at hh
      cases s with
      | positive =>
        apply positive_crossing_cell_value g hfar hbraid z a b ha hb i hbch hm he
        rw [hsort]
        exact positiveReference_imag_pos (n + 1) i halfTime h0 h1
      | negative =>
        apply negative_crossing_cell_value g hfar hbraid z a b ha hb i hbch hm he
        rw [hsort]
        have h := negativeReference_imag_neg (n + 1) i halfTime h0 h1
        change 0 < (-1 : ℝ) * (((negativeReference (n + 1) i halfTime).val i.succ).im -
          ((negativeReference (n + 1) i halfTime).val i.castSucc).im) at h
        change ((negativeReference (n + 1) i halfTime).val i.succ).im -
          ((negativeReference (n + 1) i halfTime).val i.castSucc).im < 0
        linarith
  · have hug : 1 / 2 < (u : ℝ) := lt_of_le_of_ne (le_of_not_gt hul) hu.symm
    have hvg : 1 / 2 < (v : ℝ) := hug.trans_le huv
    rw [if_neg (fun h => hul h.1)]
    exact cellTransport_eq_one_of_chamber g z a b ha hb _
      (signedReference_after n i s u hug) (signedReference_after n i s v hvg)

end BraidConverse
end

/- ReferenceSliceValueRelabel -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

theorem relabelConfig_symm_cancel {n : ℕ} (perm : Equiv.Perm (Fin n)) (z : OrderedConfig n) :
    relabelConfig perm (relabelConfig perm.symm z) = z := by
  apply Subtype.ext
  funext k
  change z.val (perm.symm (perm k)) = z.val k
  rw [Equiv.symm_apply_apply]

theorem reference_slice_value_relabel {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    (perm : Equiv.Perm (Fin (n + 1))) (z : OrderedConfig (n + 1))
    (i : Fin n) (s : BraidLetterSign) (u v : I)
    (hu : (u : ℝ) ≠ 1 / 2) (hv : (v : ℝ) ≠ 1 / 2) (huv : u ≤ v)
    (hcell : ∀ t : I, u ≤ t → t ≤ v →
      (relabelConfig perm (signedReference n i s t)).val ∈ comparisonCell z) :
    cellTransport g z (relabelConfig perm (signedReference n i s u))
      (relabelConfig perm (signedReference n i s v))
      (relabel_real_injective perm _ (signedReference_real_injective n i s u hu))
      (relabel_real_injective perm _ (signedReference_real_injective n i s v hv)) =
      if (u : ℝ) < 1 / 2 ∧ 1 / 2 < (v : ℝ) then letterValue g ⟨i, s⟩ else 1 := by
  let z' := relabelConfig perm.symm z
  have hcell' : ∀ t : I, u ≤ t → t ≤ v →
      (signedReference n i s t).val ∈ comparisonCell z' := by
    intro t hut htv
    have h := comparisonCell_relabel perm.symm z (hcell t hut htv)
    have he : (relabelConfig perm (signedReference n i s t)).val ∘ perm.symm =
        (signedReference n i s t).val := by
      funext k
      change (signedReference n i s t).val (perm (perm.symm k)) = _
      rw [Equiv.apply_symm_apply]
    exact Eq.mp (congrArg (fun w => w ∈ comparisonCell z') he) h
  have hz : relabelConfig perm z' = z := relabelConfig_symm_cancel perm z
  calc
    _ = cellTransport g (relabelConfig perm z')
        (relabelConfig perm (signedReference n i s u))
        (relabelConfig perm (signedReference n i s v))
        (relabel_real_injective perm _ (signedReference_real_injective n i s u hu))
        (relabel_real_injective perm _ (signedReference_real_injective n i s v hv)) :=
      congrArg (fun zc => cellTransport g zc
        (relabelConfig perm (signedReference n i s u))
        (relabelConfig perm (signedReference n i s v)) _ _) hz.symm
    _ = cellTransport g z' (signedReference n i s u) (signedReference n i s v)
        (signedReference_real_injective n i s u hu) (signedReference_real_injective n i s v hv) :=
      cellTransport_relabel g perm z' _ _ _ _
    _ = _ := reference_slice_value g hfar hbraid z' i s u v hu hv huv hcell'

end BraidConverse
end

/- WordSliceSupport -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)

theorem cellTransport_endpoint_congr (z a b c d : OrderedConfig (n + 1))
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hc : Function.Injective (fun i => (c.val i).re))
    (hd : Function.Injective (fun i => (d.val i).re)) (hac : a = c) (hbd : b = d) :
    cellTransport g z a b ha hb = cellTransport g z c d hc hd := by
  cases hac
  cases hbd
  rfl

theorem generic_point_congr {a b : OrderedConfig (n + 1)} (h : a = b)
    (ha : Function.Injective (fun i => (a.val i).re)) :
    Function.Injective (fun i => (b.val i).re) := by
  cases h
  exact ha

theorem cellTransport_interval_no_crossing {a b : OrderedConfig (n + 1)} (p : Path a b)
    (z : OrderedConfig (n + 1)) (u v : I) (huv : u ≤ v)
    (hu : Function.Injective (fun i => ((p u).val i).re))
    (hv : Function.Injective (fun i => ((p v).val i).re))
    (hreal : ∀ t : I, u ≤ t → t ≤ v → Function.Injective (fun i => ((p t).val i).re)) :
    cellTransport g z (p u) (p v) hu hv = 1 := by
  have hpath : ∀ t : I, Function.Injective (fun i => (((p.subpath u v) t).val i).re) := by
    intro t
    have hr : (p.subpath u v) t ∈ Set.range (p.subpath u v) := ⟨t, rfl⟩
    rw [Path.range_subpath_of_le p u v huv] at hr
    obtain ⟨s, hs, he⟩ := hr
    exact generic_point_congr he (hreal s hs.1 hs.2)
  have he := rankedRealOrder_no_crossing z (p.subpath u v) hu hv hpath
  unfold cellTransport PermutationSorting.transport
  rw [he]
  exact inv_mul_cancel _

theorem letterAfter_nonmid {n : ℕ} (w : List (BraidLetter (n + 1)))
    (a : BraidLetter (n + 1)) (t : I)
    (ht : Function.Injective (fun i => (((letterAfter w a) t).val i).re)) :
    (t : ℝ) ≠ 1 / 2 := by
  have href : Function.Injective (fun i => ((signedReference n a.index a.sign t).val i).re) := by
    intro i j hij
    apply (wordPermutation w).symm.injective
    apply ht
    change ((signedReference n a.index a.sign t).val
        (wordPermutation w ((wordPermutation w).symm i))).re =
      ((signedReference n a.index a.sign t).val
        (wordPermutation w ((wordPermutation w).symm j))).re
    simpa only [Equiv.apply_symm_apply] using hij
  intro he
  exact (signedReference_real_crossing_iff n a.index a.sign t).mpr he href

theorem letterAfter_cell_value
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    (w : List (BraidLetter (n + 1))) (a : BraidLetter (n + 1))
    (z : OrderedConfig (n + 1)) (u v : I) (huv : u ≤ v)
    (hu : Function.Injective (fun i => (((letterAfter w a) u).val i).re))
    (hv : Function.Injective (fun i => (((letterAfter w a) v).val i).re))
    (hcell : ∀ t : I, u ≤ t → t ≤ v → ((letterAfter w a) t).val ∈ comparisonCell z) :
    cellTransport g z (letterAfter w a u) (letterAfter w a v) hu hv =
      referencePartialValue g a (v : ℝ) * (referencePartialValue g a (u : ℝ))⁻¹ := by
  have hu' := letterAfter_nonmid w a u hu
  have hv' := letterAfter_nonmid w a v hv
  have h := reference_slice_value_relabel g hfar hbraid (wordPermutation w) z a.index a.sign
    u v hu' hv' huv hcell
  exact h.trans (referencePartialValue_ratio g a u v hu' hv' huv).symm

theorem word_left_cell_containment (a : BraidLetter (n + 1)) (w : List (BraidLetter (n + 1)))
    (z : OrderedConfig (n + 1)) (u v : I) (hu : (u : ℝ) ≤ 1 / 2) (hv : (v : ℝ) ≤ 1 / 2)
    (hcell : ∀ t : I, u ≤ t → t ≤ v → ((orderedWordLift (a :: w)) t).val ∈ comparisonCell z) :
    ∀ t : I, leftTime u hu ≤ t → t ≤ leftTime v hv →
      ((orderedWordLift w) t).val ∈ comparisonCell z := by
  intro t hut htv
  let s : I := ⟨(t : ℝ) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  have hs : (s : ℝ) ≤ 1 / 2 := by change (t : ℝ) / 2 ≤ 1 / 2; linarith [t.property.2]
  have hsu : u ≤ s := by
    change (u : ℝ) ≤ (t : ℝ) / 2
    change 2 * (u : ℝ) ≤ (t : ℝ) at hut
    linarith
  have hsv : s ≤ v := by
    change (t : ℝ) / 2 ≤ (v : ℝ)
    change (t : ℝ) ≤ 2 * (v : ℝ) at htv
    linarith
  have he : leftTime s hs = t := Subtype.ext (by change 2 * ((t : ℝ) / 2) = (t : ℝ); ring)
  have hp := orderedWordLift_left a w s hs
  rw [he] at hp
  exact Eq.mp (congrArg (fun x : OrderedConfig (n + 1) => x.val ∈ comparisonCell z) hp)
    (hcell s hsu hsv)

theorem word_right_cell_containment (a : BraidLetter (n + 1)) (w : List (BraidLetter (n + 1)))
    (z : OrderedConfig (n + 1)) (u v : I) (hu : 1 / 2 ≤ (u : ℝ)) (hv : 1 / 2 ≤ (v : ℝ))
    (hcell : ∀ t : I, u ≤ t → t ≤ v → ((orderedWordLift (a :: w)) t).val ∈ comparisonCell z) :
    ∀ t : I, rightTime u hu ≤ t → t ≤ rightTime v hv →
      ((letterAfter w a) t).val ∈ comparisonCell z := by
  intro t hut htv
  let s : I := ⟨((t : ℝ) + 1) / 2, by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  have hs : 1 / 2 ≤ (s : ℝ) := by change 1 / 2 ≤ ((t : ℝ) + 1) / 2; linarith [t.property.1]
  have hsu : u ≤ s := by
    change (u : ℝ) ≤ ((t : ℝ) + 1) / 2
    change 2 * (u : ℝ) - 1 ≤ (t : ℝ) at hut
    linarith
  have hsv : s ≤ v := by
    change ((t : ℝ) + 1) / 2 ≤ (v : ℝ)
    change (t : ℝ) ≤ 2 * (v : ℝ) - 1 at htv
    linarith
  have he : rightTime s hs = t := Subtype.ext (by change 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ); ring)
  have hp := orderedWordLift_right a w s hs
  rw [he] at hp
  exact Eq.mp (congrArg (fun x : OrderedConfig (n + 1) => x.val ∈ comparisonCell z) hp)
    (hcell s hsu hsv)

end BraidConverse
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

/- SortedChartShape -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

/-- The affine good-chart classification with its actual crossing time retained.
This witness lets every containing comparison cell certify the same letter sign. -/
theorem sorted_chart_shape {n : ℕ} {a b : OrderedConfig n} (p : Path a b)
    (ham : a.val ∈ realChamber (Equiv.refl (Fin n)))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (hchart : GoodChart p univ) :
    (∀ t : I, Function.Injective (fun k => ((p t).val k).re)) ∨
    ∃ i : Fin (n - 1), b.val ∈ realChamber (adjacentSwap i) ∧
      (∀ (t : I) (k l : Fin n), k < l → (k ≠ strandIdx i ∨ l ≠ strandIdxSucc i) →
        ((p t).val k).re < ((p t).val l).re) ∧
      ((∀ t : I, 0 < ((p t).val (strandIdxSucc i)).im - ((p t).val (strandIdx i)).im) ∨
       (∀ t : I, ((p t).val (strandIdxSucc i)).im - ((p t).val (strandIdx i)).im < 0)) ∧
      ∃ t : I, ((p t).val (strandIdx i)).re = ((p t).val (strandIdxSucc i)).re := by
  classical
  rcases hchart with hnone | ⟨q, hq⟩
  · exact Or.inl fun t => hnone t (mem_univ t)
  by_cases hcross : ∃ t : I, realGap q (p t).val = 0
  · obtain ⟨i, hbm, horder, hsign⟩ := sorted_pair_chart_geometry p q ham hb hp hq hcross
    obtain ⟨t, ht⟩ := hcross
    have hid : q.val.1 = strandIdx i ∧ q.val.2 = strandIdxSucc i := by
      by_contra h
      push Not at h
      have hne : q.val.1 ≠ strandIdx i ∨ q.val.2 ≠ strandIdxSucc i := by tauto
      have ho := horder t q.val.1 q.val.2 q.property hne
      exact (ne_of_lt ho) (sub_eq_zero.mp ht)
    refine Or.inr ⟨i, hbm, horder, hsign, t, ?_⟩
    have he := sub_eq_zero.mp ht
    simpa only [hid.1, hid.2] using he
  · left
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

end BraidConverse
end

/- LocalCellWord -/
section
set_option autoImplicit false
set_option maxHeartbeats 900000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)

theorem no_crossing_cell_word {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hreal : ∀ t : I, Function.Injective (fun k => ((p t).val k).re)) :
    CellTraceHasWord g p ha hb := by
  refine ⟨[], no_crossing_canonical_trace_null p ha hb hreal, ?_⟩
  intro z _
  unfold cellTransport
  rw [rankedRealOrder_no_crossing z p ha hb hreal, PermutationSorting.transport_self]
  rfl

/-- One affine good-chart edge has a common signed word whose value is certified
simultaneously by every comparison cell containing the edge. -/
theorem local_cell_word
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (hchart : GoodChart p univ) : CellTraceHasWord g p ha hb := by
  classical
  let perm := sortingPermutation a ha
  let q := p.map (relabelConfig perm).continuous
  have ha' := relabel_real_injective perm a ha
  have hb' := relabel_real_injective perm b hb
  have ham : (relabelConfig perm a).val ∈ realChamber (Equiv.refl (Fin (n + 1))) := by
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
  rcases sorted_chart_shape q ham hb' hqAffine hqChart with hnone | ⟨i, hbm, horder, hsign, t, ht⟩
  · apply no_crossing_cell_word g p ha hb
    intro t k l he
    have hkl := hnone t (a₁ := perm.symm k) (a₂ := perm.symm l)
    apply perm.symm.injective
    apply hkl
    change ((p t).val (perm (perm.symm k))).re = ((p t).val (perm (perm.symm l))).re
    simpa only [Equiv.apply_symm_apply] using he
  have hbperm : b.val ∈ realChamber (perm * PermutationSorting.adjacent n i) := by
    exact hbm
  have hgeom {w : List (BraidLetter (n + 1))}
      (h : (basedTrace (canonicalChamberApproach (relabelConfig perm a) ha')
        (q.map (configProj (n + 1)).continuous)
        (canonicalChamberApproach (relabelConfig perm b) hb')).Homotopic
          (braidWordLoop (n + 1) w)) :
      (basedTrace (canonicalChamberApproach a ha) (p.map (configProj (n + 1)).continuous)
        (canonicalChamberApproach b hb)).Homotopic (braidWordLoop (n + 1) w) :=
    Eq.mp (congrArg (fun γ => γ.Homotopic (braidWordLoop (n + 1) w))
      (canonical_trace_relabel p perm ha hb)) h
  have hcross : ((p t).val (sortingPermutation a ha i.castSucc)).re =
      ((p t).val (sortingPermutation a ha i.succ)).re := ht
  rcases hsign with hpos | hneg
  · refine ⟨[⟨i, .positive⟩], hgeom ((positive_canonical_crossing_trace q i ha' hb' ham
      hbm horder hpos).trans (letter_homotopic_singleton (⟨i, .positive⟩ : BraidLetter (n + 1)))), ?_⟩
    intro z hcell
    have hsg := (rankedRealOrder_crossing_sign z a ha i (hcell t) hcross).1.mp (hpos t)
    have hnd : ¬ (rankedRealOrder z a ha i.succ < rankedRealOrder z a ha i.castSucc) :=
      not_lt_of_ge hsg.le
    have hafter := rankedRealOrder_after_swap z ha hb i hbperm
    calc
      wordValue g [⟨i, .positive⟩] = PermutationSorting.crossingWeight g (rankedRealOrder z a ha) i := by
        simp only [wordValue, letterValue, mul_one, PermutationSorting.crossingWeight, if_neg hnd]
      _ = cellTransport g z a b ha hb := by
        rw [PermutationSorting.crossingWeight_eq_potential g hfar hbraid]
        unfold cellTransport PermutationSorting.transport
        rw [hafter]
  · refine ⟨[⟨i, .negative⟩], hgeom ((negative_canonical_crossing_trace q i ha' hb' ham
      hbm horder hneg).trans (letter_homotopic_singleton (⟨i, .negative⟩ : BraidLetter (n + 1)))), ?_⟩
    intro z hcell
    have hsg := (rankedRealOrder_crossing_sign z a ha i (hcell t) hcross).2.mp (hneg t)
    change rankedRealOrder z a ha i.succ < rankedRealOrder z a ha i.castSucc at hsg
    have hafter := rankedRealOrder_after_swap z ha hb i hbperm
    calc
      wordValue g [⟨i, .negative⟩] = PermutationSorting.crossingWeight g (rankedRealOrder z a ha) i := by
        simp only [wordValue, letterValue, mul_one, PermutationSorting.crossingWeight, if_pos hsg]
      _ = cellTransport g z a b ha hb := by
        rw [PermutationSorting.crossingWeight_eq_potential g hfar hbraid]
        unfold cellTransport PermutationSorting.transport
        rw [hafter]

end BraidConverse
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

/- CellWordCalculus -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

variable {n : ℕ} {G J : Type*} [Group G] (g : Fin n → G)
  (centers : J → OrderedConfig (n + 1))

def TraceHasCellValues {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re)) : Prop :=
  ∃ w : List (BraidLetter (n + 1)),
    (basedTrace (canonicalChamberApproach a ha) (p.map (configProj (n + 1)).continuous)
      (canonicalChamberApproach b hb)).Homotopic (braidWordLoop (n + 1) w) ∧
    ∀ j, wordValue g w = cellTransport g (centers j) a b ha hb

theorem cell_values_of_universal {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hp : CellTraceHasWord g p ha hb)
    (hcell : ∀ j t, (p t).val ∈ comparisonCell (centers j)) :
    TraceHasCellValues g centers p ha hb := by
  obtain ⟨w, hw, hv⟩ := hp
  exact ⟨w, hw, fun j => hv (centers j) (hcell j)⟩

theorem cell_values_refl (a : OrderedConfig (n + 1))
    (ha : Function.Injective (fun k => (a.val k).re)) :
    TraceHasCellValues g centers (Path.refl a) ha ha := by
  refine ⟨[], no_crossing_canonical_trace_null (Path.refl a) ha ha (fun _ => ha), ?_⟩
  intro j
  exact (PermutationSorting.transport_self g (rankedRealOrder (centers j) a ha)).symm

theorem cell_values_homotopy {a b : OrderedConfig (n + 1)} {p q : Path a b}
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (h : p.Homotopic q) (hq : TraceHasCellValues g centers q ha hb) :
    TraceHasCellValues g centers p ha hb := by
  obtain ⟨w, hw, hv⟩ := hq
  exact ⟨w, ((Path.Homotopic.refl (canonicalChamberApproach a ha)).hcomp
    ((h.map (configProj (n + 1))).hcomp
      (Path.Homotopic.refl (canonicalChamberApproach b hb).symm))).trans hw, hv⟩

theorem cell_values_cast {a b a' b' : OrderedConfig (n + 1)}
    (p : Path a b) (h0 : a' = a) (h1 : b' = b)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (ha' : Function.Injective (fun k => (a'.val k).re))
    (hb' : Function.Injective (fun k => (b'.val k).re))
    (hp : TraceHasCellValues g centers p ha hb) :
    TraceHasCellValues g centers (p.cast h0 h1) ha' hb' := by
  cases h0
  cases h1
  have he : p.cast rfl rfl = p := by
    apply Path.ext
    funext t
    rfl
  rw [he]
  exact hp

theorem cell_values_trans {a b c : OrderedConfig (n + 1)}
    (p : Path a b) (q : Path b c)
    (ha : Function.Injective (fun k => (a.val k).re))
    (hb : Function.Injective (fun k => (b.val k).re))
    (hc : Function.Injective (fun k => (c.val k).re))
    (hp : TraceHasCellValues g centers p ha hb)
    (hq : TraceHasCellValues g centers q hb hc) :
    TraceHasCellValues g centers (p.trans q) ha hc := by
  obtain ⟨u, hu, huv⟩ := hp
  obtain ⟨v, hv, hvv⟩ := hq
  have happ : (braidWordLoop (n + 1) (v ++ u)).Homotopic
      ((braidWordLoop (n + 1) u).trans (braidWordLoop (n + 1) v)) := by
    simpa only [TarchaBraids.NormalForm.wordLoop_eq_braidWordLoop] using
      wordLoop_append (braidLetterLoop (n + 1)) v u
  have ht := (basedTrace_trans (canonicalChamberApproach a ha)
    (canonicalChamberApproach b hb) (canonicalChamberApproach c hc)
    (p.map (configProj (n + 1)).continuous) (q.map (configProj (n + 1)).continuous)).trans
      ((hu.hcomp hv).trans happ.symm)
  have he := congrArg (fun γ => basedTrace (canonicalChamberApproach a ha) γ
    (canonicalChamberApproach c hc)) (Path.map_trans p q (configProj (n + 1)).continuous)
  refine ⟨v ++ u, Eq.mp (congrArg (fun γ => γ.Homotopic
    (braidWordLoop (n + 1) (v ++ u))) he.symm) ht, ?_⟩
  intro j
  rw [wordValue_append, hvv j, huv j]
  exact PermutationSorting.transport_trans g _ _ _

theorem cell_values_concat {m : ℕ} (v : Fin (m + 1) → OrderedConfig (n + 1))
    (p : (k : Fin m) → Path (v k.castSucc) (v k.succ))
    (hv : ∀ k, Function.Injective (fun i => ((v k).val i).re))
    (hp : ∀ k, TraceHasCellValues g centers (p k) (hv k.castSucc) (hv k.succ)) :
    TraceHasCellValues g centers (Path.concat v p) (hv 0) (hv (Fin.last m)) := by
  induction m with
  | zero =>
    simpa only [Path.concat_zero] using cell_values_refl g centers (v 0) (hv 0)
  | succ m ih =>
    rw [Path.concat_succ]
    exact cell_values_trans g centers _ _ (hv 0) (hv (Fin.last m).castSucc)
      (hv (Fin.last (m + 1)))
      (ih (v ∘ Fin.castSucc) (fun k => p k.castSucc) (fun k => hv k.castSucc)
        (fun k => hp k.castSucc)) (hp (Fin.last m))

end BraidConverse
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

/- ConvexCellWord -/
section
set_option autoImplicit false
set_option maxHeartbeats 900000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

variable {n : ℕ} {G J : Type*} [Group G] (g : Fin n → G)
  (centers : J → OrderedConfig (n + 1))
  (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
  (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)

include hfar hbraid

theorem simple_affine_cell_values {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hp : ∀ t : I, (p t).val = AffineMap.lineMap a.val b.val (t : ℝ))
    (hu : ∀ t (v w : StrandPair (n + 1)), realGap v (p t).val = 0 →
      realGap w (p t).val = 0 → v = w)
    (hcell : ∀ j t, (p t).val ∈ comparisonCell (centers j)) :
    TraceHasCellValues g centers p ha hb := by
  obtain ⟨m, t, ht0, ht1, _, hvertices, hchart⟩ :=
    simple_affine_chart_subdivision p ha hb hp hu
  let v : Fin (m + 1) → OrderedConfig (n + 1) := p ∘ t
  let segments : (k : Fin m) → Path (v k.castSucc) (v k.succ) :=
    fun k => p.subpath (t k.castSucc) (t k.succ)
  have hseg : ∀ k, TraceHasCellValues g centers (segments k)
      (hvertices k.castSucc) (hvertices k.succ) := by
    intro k
    apply cell_values_of_universal g centers (segments k) (hvertices k.castSucc) (hvertices k.succ)
      (local_cell_word g hfar hbraid (segments k) (hvertices k.castSucc) (hvertices k.succ)
        (affine_subpath p hp (t k.castSucc) (t k.succ)) (hchart k))
    intro j s
    exact hcell j _
  have hword := cell_values_concat g centers v segments hvertices hseg
  let h0 : a = v 0 := ((congrArg p ht0).trans p.source).symm
  let h1 : b = v (Fin.last m) := ((congrArg p ht1).trans p.target).symm
  have hcast := cell_values_cast g centers (Path.concat v segments) h0 h1
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
  exact cell_values_homotopy g centers ha hb hhom hcast

/-- A path in an open convex collision-free neighborhood has one word valid in
all the specified comparison cells containing that neighborhood. The waypoint
and every refining segment stay in their common neighborhood. -/
theorem convex_path_cell_values {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    {C : Set (Fin (n + 1) → ℂ)} (hCo : IsOpen C) (hCc : Convex ℝ C)
    (hCU : C ⊆ configurations (n + 1)) (hp : ∀ t : I, (p t).val ∈ C)
    (hCcell : ∀ j, C ⊆ comparisonCell (centers j)) :
    TraceHasCellValues g centers p ha hb := by
  obtain ⟨c, q, r, hcC, hc, hq, hr, hqu, hru, _, _, hhom⟩ :=
    convex_generic_refinement p ha hb hCo hCc hCU hp
  change OrderedConfig (n + 1) at c
  change Path a c at q
  change Path c b at r
  have haC : a.val ∈ C := by simpa only [p.source] using hp 0
  have hbC : b.val ∈ C := by simpa only [p.target] using hp 1
  have hqC : ∀ t : I, (q t).val ∈ C := by
    intro t
    exact Eq.mp (congrArg (fun x => x ∈ C) (hq t).symm)
      (hCc.lineMap_mem haC hcC t.property)
  have hrC : ∀ t : I, (r t).val ∈ C := by
    intro t
    exact Eq.mp (congrArg (fun x => x ∈ C) (hr t).symm)
      (hCc.lineMap_mem hcC hbC t.property)
  have hqv := simple_affine_cell_values g centers hfar hbraid q ha hc hq hqu
    (fun j t => hCcell j (hqC t))
  have hrv := simple_affine_cell_values g centers hfar hbraid r hc hb hr hru
    (fun j t => hCcell j (hrC t))
  exact cell_values_homotopy g centers ha hb hhom
    (cell_values_trans g centers q r ha hc hb hqv hrv)

/-- The shared-edge specialization: one finite nonempty family of incident cells
has a single word whose value agrees with every member of that family. -/
theorem finite_comparison_path_cell_values [Fintype J] [Nonempty J]
    {a b : OrderedConfig (n + 1)} (p : Path a b)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hp : ∀ j t, (p t).val ∈ comparisonCell (centers j)) :
    TraceHasCellValues g centers p ha hb := by
  classical
  let C : Set (Fin (n + 1) → ℂ) := ⋂ j : J, comparisonCell (centers j)
  have hCo : IsOpen C := isOpen_iInter_of_finite fun j => comparisonCell_open (centers j)
  have hCc : Convex ℝ C := convex_iInter fun j => comparisonCell_convex (centers j)
  have hCU : C ⊆ configurations (n + 1) := by
    intro x hx
    let j : J := Classical.choice inferInstance
    exact comparisonCell_subset_configurations (centers j) (mem_iInter.mp hx j)
  apply convex_path_cell_values g centers hfar hbraid p ha hb hCo hCc hCU
  · intro t
    exact mem_iInter.mpr fun j => hp j t
  · intro j x hx
    exact mem_iInter.mp hx j

end BraidConverse
end

/- CellTransportOverlap -/
section
set_option autoImplicit false
set_option maxHeartbeats 700000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm
open scoped Convex

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)

theorem cellTransport_trans (z a b c : OrderedConfig (n + 1))
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hc : Function.Injective (fun i => (c.val i).re)) :
    cellTransport g z b c hb hc * cellTransport g z a b ha hb =
      cellTransport g z a c ha hc :=
  PermutationSorting.transport_trans g _ _ _

theorem cellTransport_self (z a : OrderedConfig (n + 1))
    (ha : Function.Injective (fun i => (a.val i).re)) :
    cellTransport g z a a ha ha = 1 := PermutationSorting.transport_self g _

theorem cellTransport_overlap
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    (z z' a b : OrderedConfig (n + 1))
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (ha0 : a.val ∈ comparisonCell z) (ha1 : a.val ∈ comparisonCell z')
    (hb0 : b.val ∈ comparisonCell z) (hb1 : b.val ∈ comparisonCell z') :
    cellTransport g z a b ha hb = cellTransport g z' a b ha hb := by
  let C := comparisonCell z ∩ comparisonCell z'
  have hCc : Convex ℝ C := (comparisonCell_convex z).inter (comparisonCell_convex z')
  have hseg : segment ℝ a.val b.val ⊆ configurations (n + 1) :=
    (hCc.segment_subset ⟨ha0, ha1⟩ ⟨hb0, hb1⟩).trans
      (fun _ h => comparisonCell_subset_configurations z h.1)
  let p : Path a b := segmentIn a b hseg
  let centers : Bool → OrderedConfig (n + 1) := fun s => if s then z' else z
  have hpc : ∀ t : I, (p t).val ∈ C :=
    segmentIn_mem hCc ⟨ha0, ha1⟩ ⟨hb0, hb1⟩ hseg
  have hp : ∀ s t, (p t).val ∈ comparisonCell (centers s) := by
    intro s t
    cases s
    · exact (hpc t).1
    · exact (hpc t).2
  obtain ⟨w, _, hv⟩ := finite_comparison_path_cell_values g centers hfar hbraid p ha hb hp
  exact (hv false).symm.trans (hv true)

end BraidConverse
end

/- WordSliceValue -/
section
set_option autoImplicit false
set_option maxHeartbeats 900000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

theorem word_slice_value {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    (w : List (BraidLetter (n + 1))) (z : OrderedConfig (n + 1)) (u v : I)
    (hu : Function.Injective (fun i => ((orderedWordLift w u).val i).re))
    (hv : Function.Injective (fun i => ((orderedWordLift w v).val i).re))
    (huv : u ≤ v) (hmesh : (v : ℝ) - (u : ℝ) < wordMesh w)
    (hcell : ∀ t : I, u ≤ t → t ≤ v → (orderedWordLift w t).val ∈ comparisonCell z) :
    cellTransport g z (orderedWordLift w u) (orderedWordLift w v) hu hv =
      partialWordValue g w (v : ℝ) * (partialWordValue g w (u : ℝ))⁻¹ := by
  induction w generalizing z u v with
  | nil =>
    change cellTransport g z (baseOrdered (n + 1)) (baseOrdered (n + 1)) hu hv = 1 * 1⁻¹
    simpa only [inv_one, mul_one] using cellTransport_self g z (baseOrdered (n + 1)) hu
  | cons a w ih =>
    by_cases hvl : (v : ℝ) ≤ 1 / 2
    · have hul : (u : ℝ) ≤ 1 / 2 := (show (u : ℝ) ≤ (v : ℝ) from huv).trans hvl
      have heu := orderedWordLift_left a w u hul
      have hev := orderedWordLift_left a w v hvl
      have hu' := generic_point_congr heu hu
      have hv' := generic_point_congr hev hv
      have huv' : leftTime u hul ≤ leftTime v hvl := by
        change 2 * (u : ℝ) ≤ 2 * (v : ℝ)
        exact mul_le_mul_of_nonneg_left huv (by norm_num)
      have hm' : (leftTime v hvl : ℝ) - (leftTime u hul : ℝ) < wordMesh w := by
        change 2 * (v : ℝ) - 2 * (u : ℝ) < wordMesh w
        have he := wordMesh_cons a w
        nlinarith
      have hc' := word_left_cell_containment a w z u v hul hvl hcell
      rw [partialWordValue_cons_left g a w (v : ℝ) hvl,
        partialWordValue_cons_left g a w (u : ℝ) hul]
      exact (cellTransport_endpoint_congr g z _ _ _ _ hu hv hu' hv' heu hev).trans
        (ih z (leftTime u hul) (leftTime v hvl) hu' hv' huv' hm' hc')
    · by_cases hur : 1 / 2 ≤ (u : ℝ)
      · have hvr : 1 / 2 ≤ (v : ℝ) := hur.trans (show (u : ℝ) ≤ (v : ℝ) from huv)
        have heu := orderedWordLift_right a w u hur
        have hev := orderedWordLift_right a w v hvr
        have hu' := generic_point_congr heu hu
        have hv' := generic_point_congr hev hv
        have huv' : rightTime u hur ≤ rightTime v hvr := by
          change 2 * (u : ℝ) - 1 ≤ 2 * (v : ℝ) - 1
          linarith [show (u : ℝ) ≤ (v : ℝ) from huv]
        have hc' := word_right_cell_containment a w z u v hur hvr hcell
        rw [partialWordValue_cons_right g a w (v : ℝ) hvr,
          partialWordValue_cons_right g a w (u : ℝ) hur]
        calc
          _ = referencePartialValue g a (rightTime v hvr : ℝ) *
              (referencePartialValue g a (rightTime u hur : ℝ))⁻¹ :=
            (cellTransport_endpoint_congr g z _ _ _ _ hu hv hu' hv' heu hev).trans
              (letterAfter_cell_value g hfar hbraid w a z (rightTime u hur)
                (rightTime v hvr) huv' hu' hv' hc')
          _ = _ := by
            change referencePartialValue g a (2 * (v : ℝ) - 1) *
              (referencePartialValue g a (2 * (u : ℝ) - 1))⁻¹ = _
            group
      · have hum : (u : ℝ) < 1 / 2 := lt_of_not_ge hur
        have hvm : 1 / 2 < (v : ℝ) := lt_of_not_ge hvl
        have hbound := wordMesh_le (a :: w)
        have hulow : 3 / 8 < (u : ℝ) := by nlinarith
        have hvup : (v : ℝ) < 3 / 4 := by nlinarith
        have hnone : ∀ t : I, u ≤ t → t ≤ v →
            Function.Injective (fun i => ((orderedWordLift (a :: w) t).val i).re) := by
          intro t hut htv
          exact orderedWordLift_generic_around_join a w t
            (hulow.trans_le hut) (lt_of_le_of_lt htv hvup)
        have hone := cellTransport_interval_no_crossing g (orderedWordLift (a :: w)) z u v huv hu hv hnone
        have ht : 3 / 4 < 2 * (u : ℝ) := by linarith
        have href : 2 * (v : ℝ) - 1 ≤ 1 / 2 := by linarith
        rw [hone, partialWordValue_cons_right g a w (v : ℝ) hvm.le,
          partialWordValue_cons_left g a w (u : ℝ) hum.le,
          partialWordValue_after_last g w (2 * (u : ℝ)) ht]
        simp only [referencePartialValue, if_pos href, one_mul, mul_inv_cancel]

end BraidConverse
end

/- FiniteSquareGrid -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set unitInterval Metric
open BraidNormalForm

noncomputable section

namespace BraidConverse

theorem interval_distance_to_lower {m : ℕ} (hm : 0 < m) (k : Fin m) (s : I)
    (hs : s ∈ Icc (uniformTime m hm k.castSucc) (uniformTime m hm k.succ)) :
    dist s (uniformTime m hm k.castSucc) ≤ 1 / (m : ℝ) := by
  change dist (s : ℝ) (uniformTime m hm k.castSucc : ℝ) ≤ _
  have hlower : (uniformTime m hm k.castSucc : ℝ) ≤ (s : ℝ) := hs.1
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  have hgap := uniformTime_gap m hm k
  have hupper : (s : ℝ) ≤ (uniformTime m hm k.succ : ℝ) := hs.2
  linarith

/-- A finite uniform square grid can be chosen subordinate to any open cover
of the parameter square. Each whole closed grid cell lies in one cover member. -/
theorem finite_open_square_grid {J : Type*} (C : J → Set (I × I))
    (hC : ∀ j, IsOpen (C j)) (hcover : univ ⊆ ⋃ j, C j) :
    ∃ (m : ℕ) (hm : 0 < m) (chooseCell : Fin m → Fin m → J),
      ∀ i j : Fin m,
      (Icc (uniformTime m hm i.castSucc) (uniformTime m hm i.succ)) ×ˢ
        (Icc (uniformTime m hm j.castSucc) (uniformTime m hm j.succ)) ⊆
          C (chooseCell i j) := by
  classical
  obtain ⟨delta, hdelta, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (univ : Set (I × I))) hC hcover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdelta
  let m := n + 1
  have hm : 0 < m := Nat.succ_pos n
  have hmesh : 1 / (m : ℝ) < delta := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using hn
  have hc : ∀ i j : Fin m, ∃ k,
      ball (uniformTime m hm i.castSucc, uniformTime m hm j.castSucc) delta ⊆ C k :=
    fun i j => hball _ (mem_univ _)
  choose chooseCell hcell using hc
  refine ⟨m, hm, chooseCell, ?_⟩
  intro i j s hs
  apply hcell i j
  change dist s (uniformTime m hm i.castSucc, uniformTime m hm j.castSucc) < delta
  rw [Prod.dist_eq]
  exact max_lt ((interval_distance_to_lower hm i s.1 hs.1).trans_lt hmesh)
    ((interval_distance_to_lower hm j s.2 hs.2).trans_lt hmesh)

/-- Continuous parameter squares of configurations have finite comparison-cell
grids. This is a geometric foundation for the intended signed-relator converse. -/
theorem configuration_square_comparison_grid {n : ℕ} (f : I × I → configurations n)
    (hf : Continuous f) :
    ∃ (m : ℕ) (hm : 0 < m) (centers : Fin m → Fin m → configurations n),
      ∀ (i j : Fin m) (s : I × I),
        s.1 ∈ Icc (uniformTime m hm i.castSucc) (uniformTime m hm i.succ) →
        s.2 ∈ Icc (uniformTime m hm j.castSucc) (uniformTime m hm j.succ) →
        (f s).val ∈ comparisonCell (centers i j) := by
  let C : (I × I) → Set (I × I) := fun t =>
    (fun s => (f s).val) ⁻¹' comparisonCell (f t)
  have hC : ∀ t, IsOpen (C t) := fun t =>
    (comparisonCell_open (f t)).preimage (continuous_subtype_val.comp hf)
  have hcover : univ ⊆ ⋃ t, C t := by
    intro s _
    exact mem_iUnion.mpr ⟨s, comparisonCell_self (f s)⟩
  obtain ⟨m, hm, cells, hcells⟩ := finite_open_square_grid C hC hcover
  exact ⟨m, hm, fun i j => f (cells i j), fun i j s hs ht => hcells i j ⟨hs, ht⟩⟩

end BraidConverse

end
end

/- OddSquareGrid -/
section
set_option autoImplicit false

open Set unitInterval Metric BraidNormalForm

namespace BraidConverse

/-- An open square cover has arbitrarily fine subordinate grids with an odd
number of divisions, allowing interior dyadic boundary events to be avoided. -/
theorem finite_open_square_grid_odd {J : Type*} (C : J → Set (I × I))
    (hC : ∀ j, IsOpen (C j)) (hcover : univ ⊆ ⋃ j, C j)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (m : ℕ) (hm : 0 < m), Odd m ∧ 1 / (m : ℝ) < epsilon ∧
      ∃ chooseCell : Fin m → Fin m → J, ∀ i j : Fin m,
        (Icc (uniformTime m hm i.castSucc) (uniformTime m hm i.succ)) ×ˢ
          (Icc (uniformTime m hm j.castSucc) (uniformTime m hm j.succ)) ⊆
            C (chooseCell i j) := by
  classical
  obtain ⟨delta, hdelta, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (univ : Set (I × I))) hC hcover
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hdelta hepsilon)
  let m := 2 * n + 3
  have hm : 0 < m := by dsimp [m]; omega
  have hodd : Odd m := ⟨n + 1, by dsimp [m]; omega⟩
  have hmR : (n + 1 : ℝ) ≤ (m : ℝ) := by dsimp [m]; push_cast; linarith
  have hmesh : 1 / (m : ℝ) < min delta epsilon := by
    exact (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1) hmR).trans_lt
      (by simpa only [Nat.cast_add, Nat.cast_one] using hn)
  have hc : ∀ i j : Fin m, ∃ k,
      ball (uniformTime m hm i.castSucc, uniformTime m hm j.castSucc) delta ⊆ C k :=
    fun i j => hball _ (mem_univ _)
  choose chooseCell hcell using hc
  refine ⟨m, hm, hodd, lt_of_lt_of_le hmesh (min_le_right _ _), chooseCell, ?_⟩
  intro i j s hs
  apply hcell i j
  change dist s (uniformTime m hm i.castSucc, uniformTime m hm j.castSucc) < delta
  rw [Prod.dist_eq]
  have hd := lt_of_lt_of_le hmesh (min_le_left _ _)
  exact max_lt ((interval_distance_to_lower hm i s.1 hs.1).trans_lt hd)
    ((interval_distance_to_lower hm j s.2 hs.2).trans_lt hd)

end BraidConverse
end

/- OddGridDyadics -/
section
set_option autoImplicit false

open unitInterval BraidNormalForm

namespace BraidConverse

def InteriorDyadic (t : ℝ) : Prop :=
  ∃ a k : ℕ, 0 < a ∧ a < 2 ^ k ∧ t = (a : ℝ) / ((2 ^ k : ℕ) : ℝ)

theorem odd_uniformTime_ne_dyadic {m : ℕ} (hm : 0 < m) (hodd : Odd m)
    (i : Fin (m + 1)) (a k : ℕ) (ha : 0 < a) (hlt : a < 2 ^ k) :
    (uniformTime m hm i : ℝ) ≠ (a : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
  intro he
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hpR : ((2 ^ k : ℕ) : ℝ) ≠ 0 := by positivity
  change (i.val : ℝ) / m = (a : ℝ) / ((2 ^ k : ℕ) : ℝ) at he
  have heR := (div_eq_div_iff hmR hpR).mp he
  have heN : i.val * 2 ^ k = a * m := by exact_mod_cast heR
  have hdiv : 2 ^ k ∣ a * m := by
    rw [← heN]
    exact dvd_mul_left _ _
  have hc : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have hda : 2 ^ k ∣ a := hc.dvd_of_dvd_mul_right hdiv
  exact (not_le_of_gt hlt) (Nat.le_of_dvd ha hda)

theorem odd_uniformTime_not_in_dyadic_set {m : ℕ} (hm : 0 < m) (hodd : Odd m)
    (S : Set ℝ) (hS : ∀ t ∈ S, InteriorDyadic t) (i : Fin (m + 1)) :
    (uniformTime m hm i : ℝ) ∉ S := by
  intro hi
  obtain ⟨a, k, ha, hlt, he⟩ := hS _ hi
  exact odd_uniformTime_ne_dyadic hm hodd i a k ha hlt he

end BraidConverse
end

/- OrderedWordDyadics -/
section
set_option autoImplicit false

open unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

theorem InteriorDyadic.half {t : ℝ} (ht : InteriorDyadic t) : InteriorDyadic (t / 2) := by
  obtain ⟨a, k, ha, hlt, rfl⟩ := ht
  refine ⟨a, k + 1, ha, ?_, ?_⟩
  · rw [pow_succ]
    omega
  · push_cast
    rw [pow_succ]
    ring

theorem InteriorDyadic.right_half {t : ℝ} (ht : InteriorDyadic t) :
    InteriorDyadic ((t + 1) / 2) := by
  obtain ⟨a, k, ha, hlt, rfl⟩ := ht
  refine ⟨a + 2 ^ k, k + 1, by omega, ?_, ?_⟩
  · rw [pow_succ]
    omega
  · push_cast
    rw [pow_succ]
    have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp

theorem dyadic_crossings_trans {X K : Type*} [TopologicalSpace X]
    (coord : X → K → ℝ) {a b c : X} (p : Path a b) (q : Path b c)
    (hp : ∀ t : I, ¬ Function.Injective (coord (p t)) → InteriorDyadic (t : ℝ))
    (hq : ∀ t : I, ¬ Function.Injective (coord (q t)) → InteriorDyadic (t : ℝ)) :
    ∀ t : I, ¬ Function.Injective (coord ((p.trans q) t)) → InteriorDyadic (t : ℝ) := by
  intro t ht
  rw [Path.trans_apply] at ht
  split_ifs at ht with h
  · have hh := (hp _ ht).half
    convert hh using 1
    dsimp
    ring
  · have hh := (hq _ ht).right_half
    convert hh using 1
    dsimp
    ring

theorem letterAfter_crossing_dyadic {n : ℕ} (w : List (BraidLetter (n + 1)))
    (a : BraidLetter (n + 1)) (t : I)
    (ht : ¬ Function.Injective (fun i => (((letterAfter w a) t).val i).re)) :
    InteriorDyadic (t : ℝ) := by
  have href : ¬ Function.Injective (fun i => ((signedReference n a.index a.sign t).val i).re) := by
    intro h
    apply ht
    exact h.comp (wordPermutation w).injective
  have he := (signedReference_real_crossing_iff n a.index a.sign t).mp href
  exact ⟨1, 1, by decide, by decide, by simpa only [pow_one, Nat.cast_ofNat, Nat.cast_one] using he⟩

theorem orderedWordLift_crossing_dyadic {n : ℕ} (w : List (BraidLetter (n + 1))) :
    ∀ t : I, ¬ Function.Injective (fun i => (((orderedWordLift w) t).val i).re) →
      InteriorDyadic (t : ℝ) := by
  induction w with
  | nil =>
    intro t ht
    exfalso
    apply ht
    intro i j hij
    change (((i.val : ℕ) : ℂ) + 1).re = (((j.val : ℕ) : ℂ) + 1).re at hij
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re] at hij
    apply Fin.ext
    exact_mod_cast add_right_cancel hij
  | cons a w ih =>
    exact dyadic_crossings_trans (fun z : OrderedConfig (n + 1) => fun i => (z.val i).re)
      (orderedWordLift w) (letterAfter w a) ih (letterAfter_crossing_dyadic w a)

theorem orderedWordLift_generic_at_odd_grid {n m : ℕ} (w : List (BraidLetter (n + 1)))
    (hm : 0 < m) (hodd : Odd m) (i : Fin (m + 1)) :
    Function.Injective (fun j => (((orderedWordLift w) (uniformTime m hm i)).val j).re) := by
  by_contra h
  obtain ⟨a, k, ha, hlt, he⟩ := orderedWordLift_crossing_dyadic w _ h
  exact odd_uniformTime_ne_dyadic hm hodd i a k ha hlt he

end BraidConverse
end

/- OrderedWordNull -/
section
set_option autoImplicit false

open unitInterval BraidsLinksMCG TarchaBraids

namespace BraidConverse

theorem orderedWordLift_null {n : ℕ} (w : List (BraidLetter (n + 1)))
    (hw : (braidWordLoop (n + 1) w).Homotopic (Path.refl (baseUnordered (n + 1)))) :
    ∃ he : wordEnd w = baseOrdered (n + 1),
      ((orderedWordLift w).cast rfl he.symm).Homotopic (Path.refl (baseOrdered (n + 1))) := by
  obtain ⟨q, hqmap, hqnull⟩ := unordered_null_loop_lift (n + 1) (braidWordLoop (n + 1) w) hw
  have hproj : (configProj (n + 1)) ∘ (orderedWordLift w) = (configProj (n + 1)) ∘ q := by
    funext t
    have hp := congrArg (fun p : Path (baseUnordered (n + 1)) (baseUnordered (n + 1)) => p t)
      (orderedWordLift_projection w)
    have hq := congrArg (fun p : Path (baseUnordered (n + 1)) (baseUnordered (n + 1)) => p t) hqmap
    exact hp.trans hq.symm
  have hstart : orderedWordLift w 0 = q 0 :=
    (orderedWordLift w).source.trans q.source.symm
  have heq : (orderedWordLift w : I → OrderedConfig (n + 1)) = q :=
    (configProj_isCoveringMap (n + 1)).eq_of_comp_eq
      (orderedWordLift w).continuous q.continuous hproj 0 hstart
  have hend : wordEnd w = baseOrdered (n + 1) :=
    (orderedWordLift w).target.symm.trans ((congrFun heq 1).trans q.target)
  refine ⟨hend, ?_⟩
  have hepath : (orderedWordLift w).cast rfl hend.symm = q := by
    apply Path.ext
    funext t
    exact congrFun heq t
  rw [hepath]
  exact hqnull

end BraidConverse
end

/- ComparisonGridTransport -/
section
set_option autoImplicit false

open Set BraidsLinksMCG

namespace BraidConverse

variable {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
  (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
  (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)

include hfar hbraid in
theorem comparison_square_transport
    (z zB zT zL zR a b c d : OrderedConfig (n + 1))
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hc : Function.Injective (fun i => (c.val i).re))
    (hd : Function.Injective (fun i => (d.val i).re))
    (haz : a.val ∈ comparisonCell z) (hbz : b.val ∈ comparisonCell z)
    (hcz : c.val ∈ comparisonCell z) (hdz : d.val ∈ comparisonCell z)
    (haB : a.val ∈ comparisonCell zB) (hbB : b.val ∈ comparisonCell zB)
    (hcT : c.val ∈ comparisonCell zT) (hdT : d.val ∈ comparisonCell zT)
    (haL : a.val ∈ comparisonCell zL) (hcL : c.val ∈ comparisonCell zL)
    (hbR : b.val ∈ comparisonCell zR) (hdR : d.val ∈ comparisonCell zR) :
    cellTransport g zR b d hb hd * cellTransport g zB a b ha hb =
      cellTransport g zT c d hc hd * cellTransport g zL a c ha hc := by
  rw [cellTransport_overlap g hfar hbraid zR z b d hb hd hbR hbz hdR hdz,
    cellTransport_overlap g hfar hbraid zB z a b ha hb haB haz hbB hbz,
    cellTransport_overlap g hfar hbraid zT z c d hc hd hcT hcz hdT hdz,
    cellTransport_overlap g hfar hbraid zL z a c ha hc haL haz hcL hcz,
    cellTransport_trans, cellTransport_trans]

include hfar hbraid in
theorem comparison_grid_transport (m k : ℕ)
    (v : ℕ → ℕ → OrderedConfig (n + 1))
    (hv : ∀ i j, Function.Injective (fun l => ((v i j).val l).re))
    (centers Hcenter Vcenter : ℕ → ℕ → OrderedConfig (n + 1))
    (hcorner : ∀ i < m, ∀ j < k,
      (v i j).val ∈ comparisonCell (centers i j) ∧
      (v (i + 1) j).val ∈ comparisonCell (centers i j) ∧
      (v i (j + 1)).val ∈ comparisonCell (centers i j) ∧
      (v (i + 1) (j + 1)).val ∈ comparisonCell (centers i j))
    (hH : ∀ i < m, ∀ j ≤ k,
      (v i j).val ∈ comparisonCell (Hcenter i j) ∧
      (v (i + 1) j).val ∈ comparisonCell (Hcenter i j))
    (hV : ∀ i ≤ m, ∀ j < k,
      (v i j).val ∈ comparisonCell (Vcenter i j) ∧
      (v i (j + 1)).val ∈ comparisonCell (Vcenter i j)) :
    let H := fun i j => cellTransport g (Hcenter i j) (v i j) (v (i + 1) j) (hv i j) (hv (i + 1) j)
    let V := fun i j => cellTransport g (Vcenter i j) (v i j) (v i (j + 1)) (hv i j) (hv i (j + 1))
    edgeProduct (V m) k * edgeProduct (fun i => H i 0) m =
      edgeProduct (fun i => H i k) m * edgeProduct (V 0) k := by
  dsimp only
  apply rectangular_grid_transport
    (fun i j => cellTransport g (Hcenter i j) (v i j) (v (i + 1) j) (hv i j) (hv (i + 1) j))
    (fun i j => cellTransport g (Vcenter i j) (v i j) (v i (j + 1)) (hv i j) (hv i (j + 1))) m k
  intro i hi j hj
  obtain ⟨ha, hb, hc, hd⟩ := hcorner i hi j hj
  obtain ⟨haB, hbB⟩ := hH i hi j hj.le
  obtain ⟨hcT, hdT⟩ := hH i hi (j + 1) (Nat.succ_le_of_lt hj)
  obtain ⟨haL, hcL⟩ := hV i hi.le j hj
  obtain ⟨hbR, hdR⟩ := hV (i + 1) (Nat.succ_le_of_lt hi) j hj
  exact comparison_square_transport g hfar hbraid (centers i j)
    (Hcenter i j) (Hcenter i (j + 1)) (Vcenter i j) (Vcenter (i + 1) j)
    (v i j) (v (i + 1) j) (v i (j + 1)) (v (i + 1) (j + 1))
    (hv i j) (hv (i + 1) j) (hv i (j + 1)) (hv (i + 1) (j + 1))
    ha hb hc hd haB hbB hcT hdT haL hcL hbR hdR

end BraidConverse
end

/- GenericCellVertices -/
section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set BraidNormalForm

namespace BraidConverse

theorem exists_real_distinct_in_open {n : ℕ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, Function.Injective (fun i => (x i).re) := by
  obtain ⟨x, hx, hav⟩ := exists_mem_open_avoiding_linear
    (fun p : StrandPair n => realGap p) realGap_ne_zero hU hne
  refine ⟨x, hx, ?_⟩
  intro i j hij
  by_contra hneij
  rcases lt_or_gt_of_ne hneij with hlt | hgt
  · apply hav ⟨(i, j), hlt⟩
    exact sub_eq_zero.mpr hij
  · apply hav ⟨(j, i), hgt⟩
    exact sub_eq_zero.mpr hij.symm

/-- Vertices can be made real-distinct simultaneously in every incident open
cell. Any prescribed vertices that already have distinct real coordinates stay fixed. -/
theorem exists_generic_cell_vertices {V C : Type*} [Fintype C] {n : ℕ}
    (cells : C → Set (Fin n → ℂ)) (hopen : ∀ c, IsOpen (cells c))
    (incident : V → C → Prop) (original : V → Fin n → ℂ)
    (hmem : ∀ v c, incident v c → original v ∈ cells c)
    (fixed : Set V) (hfixed : ∀ v ∈ fixed,
      Function.Injective (fun i => (original v i).re)) :
    ∃ vertices : V → Fin n → ℂ,
      (∀ v, Function.Injective (fun i => (vertices v i).re)) ∧
      (∀ v c, incident v c → vertices v ∈ cells c) ∧
      (∀ v ∈ fixed, vertices v = original v) := by
  classical
  have hv : ∀ v : V, ∃ x : Fin n → ℂ,
      Function.Injective (fun i => (x i).re) ∧
      (∀ c, incident v c → x ∈ cells c) ∧ (v ∈ fixed → x = original v) := by
    intro v
    by_cases hf : v ∈ fixed
    · exact ⟨original v, hfixed v hf, hmem v, fun _ => rfl⟩
    let U : Set (Fin n → ℂ) := ⋂ c : C, if incident v c then cells c else univ
    have hU : IsOpen U := by
      apply isOpen_iInter_of_finite
      intro c
      split_ifs
      · exact hopen c
      · exact isOpen_univ
    have hUmem : original v ∈ U := by
      apply mem_iInter.mpr
      intro c
      by_cases hi : incident v c
      · simpa only [if_pos hi] using hmem v c hi
      · simp only [if_neg hi, mem_univ]
    obtain ⟨x, hx, hxi⟩ := exists_real_distinct_in_open hU ⟨original v, hUmem⟩
    refine ⟨x, hxi, ?_, fun h => (hf h).elim⟩
    intro c hi
    have hc := mem_iInter.mp hx c
    simpa only [if_pos hi] using hc
  choose vertices hvertices using hv
  exact ⟨vertices, fun v => (hvertices v).1,
    fun v => (hvertices v).2.1, fun v => (hvertices v).2.2⟩

theorem affine_edge_in_every_incident_cell {C : Type*} {n : ℕ}
    (cells : C → Set (Fin n → ℂ)) (hconvex : ∀ c, Convex ℝ (cells c))
    (a b : Fin n → ℂ) (common : C → Prop)
    (ha : ∀ c, common c → a ∈ cells c) (hb : ∀ c, common c → b ∈ cells c)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ c, common c → AffineMap.lineMap a b t ∈ cells c := by
  intro c hc
  exact (hconvex c).lineMap_mem (ha c hc) (hb c hc) ht

end BraidConverse
end

/- ConfigurationGridVertices -/
section
set_option autoImplicit false

open Set unitInterval BraidNormalForm

namespace BraidConverse

def GridIncident {m k : ℕ} (v : Fin (m + 1) × Fin (k + 1)) (c : Fin m × Fin k) : Prop :=
  (v.1 = c.1.castSucc ∨ v.1 = c.1.succ) ∧
  (v.2 = c.2.castSucc ∨ v.2 = c.2.succ)

theorem generic_configuration_grid {n m k : ℕ}
    (centers : Fin m × Fin k → configurations n)
    (original : Fin (m + 1) × Fin (k + 1) → configurations n)
    (hcorner : ∀ v c, GridIncident v c → (original v).val ∈ comparisonCell (centers c))
    (fixed : Set (Fin (m + 1) × Fin (k + 1)))
    (hfixed : ∀ v ∈ fixed, Function.Injective (fun i => ((original v).val i).re)) :
    ∃ vertices : Fin (m + 1) × Fin (k + 1) → configurations n,
      (∀ v, Function.Injective (fun i => ((vertices v).val i).re)) ∧
      (∀ v c, GridIncident v c → (vertices v).val ∈ comparisonCell (centers c)) ∧
      (∀ v ∈ fixed, vertices v = original v) := by
  obtain ⟨points, hreal, hmem, heq⟩ := exists_generic_cell_vertices
    (fun c => comparisonCell (centers c)) (fun c => comparisonCell_open (centers c))
    GridIncident (fun v => (original v).val) hcorner fixed hfixed
  let vertices : Fin (m + 1) × Fin (k + 1) → configurations n := fun v =>
    ⟨points v, fun i j hij => hreal v (congrArg Complex.re hij)⟩
  refine ⟨vertices, hreal, hmem, ?_⟩
  intro v hv
  exact Subtype.ext (heq v hv)

theorem sampled_square_corner_membership {n m : ℕ} (hm : 0 < m)
    (f : I × I → configurations n) (centers : Fin m → Fin m → configurations n)
    (hc : ∀ (i j : Fin m) (s : I × I),
      s.1 ∈ Icc (uniformTime m hm i.castSucc) (uniformTime m hm i.succ) →
      s.2 ∈ Icc (uniformTime m hm j.castSucc) (uniformTime m hm j.succ) →
      (f s).val ∈ comparisonCell (centers i j)) :
    ∀ (v : Fin (m + 1) × Fin (m + 1)) (c : Fin m × Fin m), GridIncident v c →
      (f (uniformTime m hm v.1, uniformTime m hm v.2)).val ∈
        comparisonCell (centers c.1 c.2) := by
  intro v c hv
  have hmono := (uniformTime_strictMono m hm).monotone
  have hfirst : uniformTime m hm c.1.castSucc ≤ uniformTime m hm c.1.succ :=
    hmono (by change c.1.val ≤ c.1.val + 1; omega)
  have hsecond : uniformTime m hm c.2.castSucc ≤ uniformTime m hm c.2.succ :=
    hmono (by change c.2.val ≤ c.2.val + 1; omega)
  apply hc c.1 c.2
  · rcases hv.1 with h | h
    · rw [h]; exact ⟨le_rfl, hfirst⟩
    · rw [h]; exact ⟨hfirst, le_rfl⟩
  · rcases hv.2 with h | h
    · rw [h]; exact ⟨le_rfl, hsecond⟩
    · rw [h]; exact ⟨hsecond, le_rfl⟩

end BraidConverse
end

/- FiniteComparisonGrid -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set BraidsLinksMCG

namespace BraidConverse

def gridIndex (m k : ℕ) : Fin (m + 1) := ⟨min k m, Nat.lt_succ_of_le (min_le_right _ _)⟩

def gridCellIndex (m : ℕ) (hm : 0 < m) (k : ℕ) : Fin m :=
  ⟨min k (m - 1), by omega⟩

theorem gridIndex_incident (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k ≤ m) :
    gridIndex m k = (gridCellIndex m hm k).castSucc ∨
      gridIndex m k = (gridCellIndex m hm k).succ := by
  by_cases hlt : k < m
  · left
    apply Fin.ext
    dsimp [gridIndex, gridCellIndex]
    omega
  · right
    apply Fin.ext
    dsimp [gridIndex, gridCellIndex]
    omega

theorem gridIndex_low (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m) :
    gridIndex m k = (gridCellIndex m hm k).castSucc := by
  apply Fin.ext
  dsimp [gridIndex, gridCellIndex]
  omega

theorem gridIndex_high (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m) :
    gridIndex m (k + 1) = (gridCellIndex m hm k).succ := by
  apply Fin.ext
  dsimp [gridIndex, gridCellIndex]
  omega

theorem gridIndex_zero (m : ℕ) : gridIndex m 0 = 0 := by
  apply Fin.ext
  simp [gridIndex]

theorem gridIndex_last (m : ℕ) : gridIndex m m = Fin.last m := by
  apply Fin.ext
  simp [gridIndex]

theorem gridCellIndex_lt (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : k < m) :
    gridCellIndex m hm k = ⟨k, hk⟩ := by
  apply Fin.ext
  dsimp [gridCellIndex]
  omega

theorem cellTransport_eq_one_of_eq {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (z a b : OrderedConfig (n + 1))
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re)) (hab : a = b) :
    cellTransport g z a b ha hb = 1 := by
  cases hab
  exact cellTransport_self g z a ha

/-- Finite-index geometric grid cancellation, with all three non-bottom sides
fixed at one generic base configuration. -/
theorem finite_comparison_grid_bottom {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    (m : ℕ) (hm : 0 < m)
    (v : Fin (m + 1) × Fin (m + 1) → OrderedConfig (n + 1))
    (hv : ∀ x, Function.Injective (fun l => ((v x).val l).re))
    (centers : Fin m × Fin m → OrderedConfig (n + 1))
    (hmem : ∀ x c, GridIncident x c → (v x).val ∈ comparisonCell (centers c))
    (a : OrderedConfig (n + 1))
    (hleft : ∀ j, v (0, j) = a) (hright : ∀ j, v (Fin.last m, j) = a)
    (htop : ∀ i, v (i, Fin.last m) = a) :
    let bottom : ℕ → G := fun i =>
      cellTransport g (centers (gridCellIndex m hm i, gridCellIndex m hm 0))
        (v (gridIndex m i, 0)) (v (gridIndex m (i + 1), 0))
        (hv (gridIndex m i, 0)) (hv (gridIndex m (i + 1), 0))
    edgeProduct bottom m = 1 := by
  let Vtx : ℕ → ℕ → OrderedConfig (n + 1) := fun i j => v (gridIndex m i, gridIndex m j)
  let Cen : ℕ → ℕ → OrderedConfig (n + 1) := fun i j =>
    centers (gridCellIndex m hm i, gridCellIndex m hm j)
  have hVtx : ∀ i j, Function.Injective (fun l => ((Vtx i j).val l).re) :=
    fun i j => hv (gridIndex m i, gridIndex m j)
  have hcorner : ∀ i < m, ∀ j < m,
      (Vtx i j).val ∈ comparisonCell (Cen i j) ∧
      (Vtx (i + 1) j).val ∈ comparisonCell (Cen i j) ∧
      (Vtx i (j + 1)).val ∈ comparisonCell (Cen i j) ∧
      (Vtx (i + 1) (j + 1)).val ∈ comparisonCell (Cen i j) := by
    intro i hi j hj
    have h0 := gridIndex_low m hm i hi
    have h1 := gridIndex_high m hm i hi
    have h2 := gridIndex_low m hm j hj
    have h3 := gridIndex_high m hm j hj
    exact ⟨hmem _ _ ⟨Or.inl h0, Or.inl h2⟩,
      hmem _ _ ⟨Or.inr h1, Or.inl h2⟩,
      hmem _ _ ⟨Or.inl h0, Or.inr h3⟩,
      hmem _ _ ⟨Or.inr h1, Or.inr h3⟩⟩
  have hH : ∀ i < m, ∀ j ≤ m,
      (Vtx i j).val ∈ comparisonCell (Cen i j) ∧
      (Vtx (i + 1) j).val ∈ comparisonCell (Cen i j) := by
    intro i hi j hj
    exact ⟨hmem _ _ ⟨Or.inl (gridIndex_low m hm i hi), gridIndex_incident m hm j hj⟩,
      hmem _ _ ⟨Or.inr (gridIndex_high m hm i hi), gridIndex_incident m hm j hj⟩⟩
  have hV : ∀ i ≤ m, ∀ j < m,
      (Vtx i j).val ∈ comparisonCell (Cen i j) ∧
      (Vtx i (j + 1)).val ∈ comparisonCell (Cen i j) := by
    intro i hi j hj
    exact ⟨hmem _ _ ⟨gridIndex_incident m hm i hi, Or.inl (gridIndex_low m hm j hj)⟩,
      hmem _ _ ⟨gridIndex_incident m hm i hi, Or.inr (gridIndex_high m hm j hj)⟩⟩
  let H := fun i j => cellTransport g (Cen i j) (Vtx i j) (Vtx (i + 1) j)
    (hVtx i j) (hVtx (i + 1) j)
  let V := fun i j => cellTransport g (Cen i j) (Vtx i j) (Vtx i (j + 1))
    (hVtx i j) (hVtx i (j + 1))
  have hgrid : edgeProduct (V m) m * edgeProduct (fun i => H i 0) m =
      edgeProduct (fun i => H i m) m * edgeProduct (V 0) m :=
    comparison_grid_transport g hfar hbraid m m Vtx hVtx Cen Cen Cen hcorner hH hV
  have hl : ∀ j < m, V 0 j = 1 := by
    intro j _
    apply cellTransport_eq_one_of_eq
    exact (by simpa only [Vtx, gridIndex_zero] using
      (hleft (gridIndex m j)).trans (hleft (gridIndex m (j + 1))).symm)
  have hr : ∀ j < m, V m j = 1 := by
    intro j _
    apply cellTransport_eq_one_of_eq
    exact (by simpa only [Vtx, gridIndex_last] using
      (hright (gridIndex m j)).trans (hright (gridIndex m (j + 1))).symm)
  have ht : ∀ i < m, H i m = 1 := by
    intro i _
    apply cellTransport_eq_one_of_eq
    exact (by simpa only [Vtx, gridIndex_last] using
      (htop (gridIndex m i)).trans (htop (gridIndex m (i + 1))).symm)
  have hbot : edgeProduct (fun i => H i 0) m = 1 := by
    simpa only [edgeProduct_eq_one _ _ hl, edgeProduct_eq_one _ _ hr,
      edgeProduct_eq_one _ _ ht, one_mul, mul_one] using hgrid
  simpa only [H, Vtx, Cen, gridIndex_zero] using hbot

end BraidConverse
end

/- NullSquareGrid -/
section
set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set unitInterval BraidsLinksMCG BraidNormalForm

namespace BraidConverse

theorem cellTransport_congr_endpoints {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (z a b c d : OrderedConfig (n + 1))
    (ha : Function.Injective (fun i => (a.val i).re))
    (hb : Function.Injective (fun i => (b.val i).re))
    (hc : Function.Injective (fun i => (c.val i).re))
    (hd : Function.Injective (fun i => (d.val i).re)) (hac : a = c) (hbd : b = d) :
    cellTransport g z a b ha hb = cellTransport g z c d hc hd := by
  cases hac
  cases hbd
  rfl

/-- A based null square has arbitrarily fine odd bottom subdivisions whose
actual comparison-cell transports multiply to one. Interior vertices alone are
perturbed, within every incident cell; all boundary samples are preserved. -/
theorem based_square_bottom_transport {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    {a : OrderedConfig (n + 1)} (q : Path a a)
    (ha : Function.Injective (fun i => (a.val i).re))
    (F : C(I × I, OrderedConfig (n + 1)))
    (hbottom : ∀ t : I, F (t, 0) = q t)
    (htop : ∀ t : I, F (t, 1) = a)
    (hleft : ∀ t : I, F (0, t) = a)
    (hright : ∀ t : I, F (1, t) = a)
    (hgeneric : ∀ (m : ℕ) (hm : 0 < m), Odd m → ∀ k : Fin (m + 1),
      Function.Injective (fun i => ((q (uniformTime m hm k)).val i).re))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (m : ℕ) (hm : 0 < m) (hodd : Odd m)
      (bottomCenters : Fin m → OrderedConfig (n + 1)) (bottom : ℕ → G),
      1 / (m : ℝ) < epsilon ∧
      (∀ (i : Fin m) (t : I), t ∈ Icc (uniformTime m hm i.castSucc)
        (uniformTime m hm i.succ) → (q t).val ∈ comparisonCell (bottomCenters i)) ∧
      (∀ (i : ℕ) (hi : i < m), bottom i =
        cellTransport g (bottomCenters ⟨i, hi⟩)
          (q (uniformTime m hm (⟨i, hi⟩ : Fin m).castSucc))
          (q (uniformTime m hm (⟨i, hi⟩ : Fin m).succ))
          (hgeneric m hm hodd (⟨i, hi⟩ : Fin m).castSucc)
          (hgeneric m hm hodd (⟨i, hi⟩ : Fin m).succ)) ∧
      edgeProduct bottom m = 1 := by
  classical
  let cover : (I × I) → Set (I × I) := fun t =>
    (fun s => (F s).val) ⁻¹' comparisonCell (F t)
  have hopen : ∀ t, IsOpen (cover t) := fun t =>
    (comparisonCell_open (F t)).preimage (continuous_subtype_val.comp F.continuous)
  have hcover : univ ⊆ ⋃ t, cover t := by
    intro s _
    exact mem_iUnion.mpr ⟨s, comparisonCell_self (F s)⟩
  obtain ⟨m, hm, hodd, hmesh, chooseCell, hchoose⟩ :=
    finite_open_square_grid_odd cover hopen hcover hepsilon
  let centers : Fin m × Fin m → OrderedConfig (n + 1) := fun c => F (chooseCell c.1 c.2)
  have hc : ∀ (i j : Fin m) (s : I × I),
      s.1 ∈ Icc (uniformTime m hm i.castSucc) (uniformTime m hm i.succ) →
      s.2 ∈ Icc (uniformTime m hm j.castSucc) (uniformTime m hm j.succ) →
      (F s).val ∈ comparisonCell (centers (i, j)) :=
    fun i j s hs ht => hchoose i j ⟨hs, ht⟩
  let original : Fin (m + 1) × Fin (m + 1) → OrderedConfig (n + 1) := fun v =>
    F (uniformTime m hm v.1, uniformTime m hm v.2)
  have hoL (j : Fin (m + 1)) : original (0, j) = a := by
    simpa only [original, uniformTime_zero] using hleft (uniformTime m hm j)
  have hoR (j : Fin (m + 1)) : original (Fin.last m, j) = a := by
    simpa only [original, uniformTime_last] using hright (uniformTime m hm j)
  have hoT (i : Fin (m + 1)) : original (i, Fin.last m) = a := by
    simpa only [original, uniformTime_last] using htop (uniformTime m hm i)
  have hoB (i : Fin (m + 1)) : original (i, 0) = q (uniformTime m hm i) := by
    simpa only [original, uniformTime_zero] using hbottom (uniformTime m hm i)
  let fixed : Set (Fin (m + 1) × Fin (m + 1)) :=
    {v | v.1 = 0 ∨ v.1 = Fin.last m ∨ v.2 = 0 ∨ v.2 = Fin.last m}
  have hfixed : ∀ v ∈ fixed, Function.Injective (fun i => ((original v).val i).re) := by
    rintro ⟨i, j⟩ (h | h | h | h)
    · change i = 0 at h
      subst i
      rw [hoL]
      exact ha
    · change i = Fin.last m at h
      subst i
      rw [hoR]
      exact ha
    · change j = 0 at h
      subst j
      rw [hoB]
      exact hgeneric m hm hodd i
    · change j = Fin.last m at h
      subst j
      rw [hoT]
      exact ha
  have hcorner : ∀ v c, GridIncident v c → (original v).val ∈ comparisonCell (centers c) :=
    sampled_square_corner_membership hm F (fun i j => centers (i, j)) hc
  obtain ⟨v, hv, hvmem, hvfix⟩ := generic_configuration_grid centers original hcorner fixed hfixed
  change (Fin (m + 1) × Fin (m + 1) → OrderedConfig (n + 1)) at v
  have hvL (j : Fin (m + 1)) : v (0, j) = a :=
    (hvfix (0, j) (Or.inl rfl)).trans (hoL j)
  have hvR (j : Fin (m + 1)) : v (Fin.last m, j) = a :=
    (hvfix (Fin.last m, j) (Or.inr (Or.inl rfl))).trans (hoR j)
  have hvT (i : Fin (m + 1)) : v (i, Fin.last m) = a :=
    (hvfix (i, Fin.last m) (Or.inr (Or.inr (Or.inr rfl)))).trans (hoT i)
  have hvB (i : Fin (m + 1)) : v (i, 0) = q (uniformTime m hm i) :=
    (hvfix (i, 0) (Or.inr (Or.inr (Or.inl rfl)))).trans (hoB i)
  let bottomCenters : Fin m → OrderedConfig (n + 1) := fun i => centers (i, ⟨0, hm⟩)
  let bottom : ℕ → G := fun i =>
    cellTransport g (centers (gridCellIndex m hm i, gridCellIndex m hm 0))
      (v (gridIndex m i, 0)) (v (gridIndex m (i + 1), 0))
      (hv (gridIndex m i, 0)) (hv (gridIndex m (i + 1), 0))
  have hprod : edgeProduct bottom m = 1 :=
    finite_comparison_grid_bottom g hfar hbraid m hm v hv centers hvmem a hvL hvR hvT
  refine ⟨m, hm, hodd, bottomCenters, bottom, hmesh, ?_, ?_, hprod⟩
  · intro i t ht
    have h0 : (0 : I) ∈ Icc (uniformTime m hm (⟨0, hm⟩ : Fin m).castSucc)
        (uniformTime m hm (⟨0, hm⟩ : Fin m).succ) := by
      change (0 : I) ∈ Icc (uniformTime m hm 0) _
      rw [uniformTime_zero]
      exact ⟨le_rfl, (uniformTime m hm (⟨0, hm⟩ : Fin m).succ).property.1⟩
    have hh := hc i ⟨0, hm⟩ (t, 0) ht h0
    exact Eq.mp (congrArg (fun x => x.val ∈ comparisonCell (bottomCenters i)) (hbottom t)) hh
  · intro i hi
    have h0 : gridIndex m i = (⟨i, hi⟩ : Fin m).castSucc := by
      apply Fin.ext
      dsimp [gridIndex]
      omega
    have h1 : gridIndex m (i + 1) = (⟨i, hi⟩ : Fin m).succ := by
      apply Fin.ext
      dsimp [gridIndex]
      omega
    have he0 : v (gridIndex m i, 0) = q (uniformTime m hm (⟨i, hi⟩ : Fin m).castSucc) :=
      (hvB (gridIndex m i)).trans (congrArg (fun k => q (uniformTime m hm k)) h0)
    have he1 : v (gridIndex m (i + 1), 0) = q (uniformTime m hm (⟨i, hi⟩ : Fin m).succ) :=
      (hvB (gridIndex m (i + 1))).trans (congrArg (fun k => q (uniformTime m hm k)) h1)
    have hc0 : gridCellIndex m hm 0 = ⟨0, hm⟩ := gridCellIndex_lt m hm 0 hm
    dsimp only [bottom, bottomCenters]
    rw [gridCellIndex_lt m hm i hi, hc0]
    exact cellTransport_congr_endpoints g _ _ _ _ _ _ _ _ _ he0 he1

theorem null_loop_bottom_transport {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    {a : OrderedConfig (n + 1)} (q : Path a a)
    (ha : Function.Injective (fun i => (a.val i).re))
    (hq : q.Homotopic (Path.refl a))
    (hgeneric : ∀ (m : ℕ) (hm : 0 < m), Odd m → ∀ k : Fin (m + 1),
      Function.Injective (fun i => ((q (uniformTime m hm k)).val i).re))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ (m : ℕ) (hm : 0 < m) (hodd : Odd m)
      (bottomCenters : Fin m → OrderedConfig (n + 1)) (bottom : ℕ → G),
      1 / (m : ℝ) < epsilon ∧
      (∀ (i : Fin m) (t : I), t ∈ Icc (uniformTime m hm i.castSucc)
        (uniformTime m hm i.succ) → (q t).val ∈ comparisonCell (bottomCenters i)) ∧
      (∀ (i : ℕ) (hi : i < m), bottom i =
        cellTransport g (bottomCenters ⟨i, hi⟩)
          (q (uniformTime m hm (⟨i, hi⟩ : Fin m).castSucc))
          (q (uniformTime m hm (⟨i, hi⟩ : Fin m).succ))
          (hgeneric m hm hodd (⟨i, hi⟩ : Fin m).castSucc)
          (hgeneric m hm hodd (⟨i, hi⟩ : Fin m).succ)) ∧
      edgeProduct bottom m = 1 := by
  obtain ⟨H⟩ := hq
  let F : C(I × I, OrderedConfig (n + 1)) :=
    ⟨fun s => H (s.2, s.1), H.continuous.comp continuous_swap⟩
  apply based_square_bottom_transport g hfar hbraid q ha F
    (fun t => H.apply_zero t) (fun t => H.apply_one t)
    (fun t => H.source t) (fun t => H.target t) hgeneric hepsilon

end BraidConverse
end

/- ArtinSortingTransport -/
section
set_option autoImplicit false

namespace BraidConverse

open BraidsLinksMCG

def artinGenerator {n : ℕ} (i : Fin n) : ArtinBraidGroup (n + 1) := sigma i

theorem artinGenerator_far {n : ℕ} (i j : Fin n) (hij : i.val + 1 < j.val) :
    Commute (artinGenerator i) (artinGenerator j) := by
  have habs : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs := by omega
  have hr : FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹ ∈
      braidRels (n + 1) := Or.inl ⟨i, j, habs, rfl⟩
  have h := PresentedGroup.one_of_mem hr
  simp only [map_mul, map_inv] at h
  change artinGenerator i * artinGenerator j * (artinGenerator i)⁻¹ *
    (artinGenerator j)⁻¹ = 1 at h
  change artinGenerator i * artinGenerator j = artinGenerator j * artinGenerator i
  calc
    artinGenerator i * artinGenerator j =
        (artinGenerator i * artinGenerator j * (artinGenerator i)⁻¹ *
          (artinGenerator j)⁻¹) * (artinGenerator j * artinGenerator i) := by group
    _ = artinGenerator j * artinGenerator i := by rw [h, one_mul]

theorem artinGenerator_braid {n : ℕ} (i j : Fin n) (hij : j.val = i.val + 1) :
    artinGenerator i * artinGenerator j * artinGenerator i =
      artinGenerator j * artinGenerator i * artinGenerator j := by
  have hr : FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹ ∈ braidRels (n + 1) :=
    Or.inr ⟨i, j, hij, rfl⟩
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem hr
  simp only [map_mul] at h
  exact h

theorem artin_crossing_potential {n : ℕ} (p : PermutationSorting.Permutation n) (i : Fin n) :
    PermutationSorting.crossingWeight artinGenerator p i =
      (PermutationSorting.potential artinGenerator (PermutationSorting.swapAt p i))⁻¹ *
        PermutationSorting.potential artinGenerator p :=
  PermutationSorting.crossingWeight_eq_potential artinGenerator
    artinGenerator_far artinGenerator_braid p i

end BraidConverse
end

/- SignedRelatorTrace -/
section
set_option autoImplicit false

namespace BraidConverseRepair

variable {G : Type*} [Group G]

/-- The local repair permits either orientation of each defining relator. -/
inductive SignedRelatorTrace (R : Set G) : G → Prop where
  | nil : SignedRelatorTrace R 1
  | step {w u r : G} : SignedRelatorTrace R w → (r ∈ R ∨ r⁻¹ ∈ R) →
      SignedRelatorTrace R (u * r * u⁻¹ * w)

namespace SignedRelatorTrace

variable {R : Set G}

theorem mul {a b : G} (ha : SignedRelatorTrace R a) (hb : SignedRelatorTrace R b) :
    SignedRelatorTrace R (a * b) := by
  induction ha with
  | nil => simpa only [one_mul] using hb
  | @step w u r hw hr ih =>
    simpa only [mul_assoc] using (SignedRelatorTrace.step (u := u) (r := r) ih hr)

theorem inv {a : G} (ha : SignedRelatorTrace R a) : SignedRelatorTrace R a⁻¹ := by
  induction ha with
  | nil => simpa only [inv_one] using (SignedRelatorTrace.nil (R := R))
  | @step w u r hw hr ih =>
    have hr' : r⁻¹ ∈ R ∨ (r⁻¹)⁻¹ ∈ R := by
      rcases hr with h | h
      · exact Or.inr (by simpa only [inv_inv] using h)
      · exact Or.inl h
    have h := SignedRelatorTrace.step (u := w⁻¹ * u) (r := r⁻¹) ih hr'
    convert h using 1
    group

theorem mem_normalClosure {a : G} (ha : SignedRelatorTrace R a) :
    a ∈ Subgroup.normalClosure R := by
  induction ha with
  | nil => exact (Subgroup.normalClosure R).one_mem
  | @step w u r hw hr ih =>
    have hr' : r ∈ Subgroup.normalClosure R := by
      rcases hr with h | h
      · exact Subgroup.subset_normalClosure h
      · simpa only [inv_inv] using
          (Subgroup.normalClosure R).inv_mem (Subgroup.subset_normalClosure h)
    exact (Subgroup.normalClosure R).mul_mem
      ((inferInstance : (Subgroup.normalClosure R).Normal).conj_mem r hr' u) ih

theorem of_mem_normalClosure {a : G} (ha : a ∈ Subgroup.normalClosure R) :
    SignedRelatorTrace R a := by
  change a ∈ Subgroup.closure (Group.conjugatesOfSet R) at ha
  apply Subgroup.closure_induction (p := fun a _ => SignedRelatorTrace R a)
    ?_ SignedRelatorTrace.nil (fun _ _ _ _ h₁ h₂ => h₁.mul h₂)
    (fun _ _ h => h.inv) ha
  intro x hx
  obtain ⟨r, hr, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨u, hu⟩ := isConj_iff.mp hc
  rw [← hu]
  simpa only [mul_one] using (SignedRelatorTrace.step (w := 1) (u := u) (r := r)
    SignedRelatorTrace.nil (Or.inl hr))

theorem iff_mem_normalClosure (R : Set G) (a : G) :
    SignedRelatorTrace R a ↔ a ∈ Subgroup.normalClosure R :=
  ⟨mem_normalClosure, of_mem_normalClosure⟩

theorem iff_presented_mk_eq_one {A : Type*} (R : Set (FreeGroup A)) (w : FreeGroup A) :
    SignedRelatorTrace R w ↔ PresentedGroup.mk R w = 1 :=
  (iff_mem_normalClosure R w).trans PresentedGroup.mk_eq_one_iff.symm

end SignedRelatorTrace

end BraidConverseRepair
end

/- WordPresentationBridge -/
section
set_option autoImplicit false

open BraidsLinksMCG TarchaBraids

namespace BraidConverse

theorem braidWordFree_append {n : ℕ} (v w : List (BraidLetter n)) :
    braidWordFree (v ++ w) = braidWordFree v * braidWordFree w := by
  induction v with
  | nil => simp only [List.nil_append, braidWordFree, one_mul]
  | cons a v ih => simp only [List.cons_append, braidWordFree, ih, mul_assoc]

theorem exists_word_of_free {n : ℕ} (x : FreeGroup (Fin (n - 1))) :
    ∃ w : List (BraidLetter n), braidWordFree w = x := by
  induction x using FreeGroup.induction_on with
  | C1 => exact ⟨[], rfl⟩
  | of i => exact ⟨[⟨i, .positive⟩], by simp only [braidWordFree, braidLetterFree, mul_one]⟩
  | inv_of i _ => exact ⟨[⟨i, .negative⟩], by simp only [braidWordFree, braidLetterFree, mul_one]⟩
  | mul x y hx hy =>
    obtain ⟨v, hv⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨v ++ w, by rw [braidWordFree_append, hv, hw]⟩

theorem letterValue_artin {n : ℕ} (a : BraidLetter (n + 1)) :
    letterValue artinGenerator a = PresentedGroup.mk (braidRels (n + 1)) (braidLetterFree a) := by
  rcases a with ⟨i, sign⟩
  cases sign <;> simp only [letterValue, braidLetterFree, map_inv] <;> rfl

theorem wordValue_artin {n : ℕ} (w : List (BraidLetter (n + 1))) :
    wordValue artinGenerator w = PresentedGroup.mk (braidRels (n + 1)) (braidWordFree w) := by
  induction w with
  | nil => exact (map_one _).symm
  | cons a w ih =>
    simp only [wordValue, braidWordFree, map_mul, letterValue_artin, ih]
    rfl

theorem letter_geometric_evaluation {n : ℕ} (a : BraidLetter n) :
    FreeGroup.lift (halfTwistBraid n) (braidLetterFree a) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (braidLetterLoop n a)) := by
  rcases a with ⟨i, sign⟩
  cases sign <;> simp only [braidLetterFree, braidLetterLoop, map_inv,
    FreeGroup.lift_apply_of, halfTwistBraid, FundamentalGroup.inv_def,
    Path.Homotopic.Quotient.mk_symm] <;> rfl

theorem word_geometric_evaluation {n : ℕ} (w : List (BraidLetter n)) :
    FreeGroup.lift (halfTwistBraid n) (braidWordFree w) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (braidWordLoop n w)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [braidWordFree, braidWordLoop, map_mul, letter_geometric_evaluation, ih]
    rfl

theorem null_free_word_has_null_loop {n : ℕ} (x : FreeGroup (Fin (n - 1)))
    (hx : FreeGroup.lift (halfTwistBraid n) x = 1) :
    ∃ w : List (BraidLetter n), braidWordFree w = x ∧
      (braidWordLoop n w).Homotopic (Path.refl (baseUnordered n)) := by
  obtain ⟨w, hw⟩ := exists_word_of_free x
  refine ⟨w, hw, ?_⟩
  have h : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (braidWordLoop n w)) = 1 := by
    rw [← word_geometric_evaluation, hw]
    exact hx
  exact Path.Homotopic.Quotient.eq.mp h

theorem wordValue_one_iff_signed_trace {n : ℕ} (w : List (BraidLetter (n + 1))) :
    wordValue artinGenerator w = 1 ↔
      BraidConverseRepair.SignedRelatorTrace (braidRels (n + 1)) (braidWordFree w) := by
  rw [wordValue_artin]
  exact (BraidConverseRepair.SignedRelatorTrace.iff_presented_mk_eq_one _ _).symm

end BraidConverse
end

/- NullWordConverse -/
section
set_option autoImplicit false
set_option maxHeartbeats 900000

open Set unitInterval BraidsLinksMCG TarchaBraids BraidNormalForm

namespace BraidConverse

theorem word_value_of_null_loop {n : ℕ} {G : Type*} [Group G] (g : Fin n → G)
    (hfar : ∀ i j : Fin n, i.val + 1 < j.val → Commute (g i) (g j))
    (hbraid : ∀ i j : Fin n, j.val = i.val + 1 → g i * g j * g i = g j * g i * g j)
    (w : List (BraidLetter (n + 1)))
    (hw : (braidWordLoop (n + 1) w).Homotopic (Path.refl (baseUnordered (n + 1)))) :
    wordValue g w = 1 := by
  obtain ⟨hend, hnull⟩ := orderedWordLift_null w hw
  let q : Path (baseOrdered (n + 1)) (baseOrdered (n + 1)) :=
    (orderedWordLift w).cast rfl hend.symm
  have hgeneric : ∀ (m : ℕ) (hm : 0 < m), Odd m → ∀ k : Fin (m + 1),
      Function.Injective (fun i => ((q (uniformTime m hm k)).val i).re) :=
    fun m hm hodd k => orderedWordLift_generic_at_odd_grid w hm hodd k
  obtain ⟨m, hm, hodd, centers, bottom, hmesh, hcells, hvalues, hprod⟩ :=
    null_loop_bottom_transport g hfar hbraid q (base_real_injective (n + 1)) hnull
      hgeneric (wordMesh_pos w)
  let P : ℕ → G := fun i => partialWordValue g w (uniformTime m hm (gridIndex m i) : ℝ)
  have he : ∀ i < m, bottom i = P (i + 1) * (P i)⁻¹ := by
    intro i hi
    let k : Fin m := ⟨i, hi⟩
    have h0 : gridIndex m i = k.castSucc := by
      apply Fin.ext
      simp only [gridIndex, k, Fin.val_castSucc, Nat.min_eq_left hi.le]
    have h1 : gridIndex m (i + 1) = k.succ := by
      apply Fin.ext
      simp only [gridIndex, k, Fin.val_succ, Nat.min_eq_left (Nat.succ_le_of_lt hi)]
    have huv : uniformTime m hm k.castSucc ≤ uniformTime m hm k.succ :=
      (uniformTime_strictMono m hm).monotone (by change i ≤ i + 1; omega)
    have hgap : (uniformTime m hm k.succ : ℝ) - (uniformTime m hm k.castSucc : ℝ) < wordMesh w := by
      rw [uniformTime_gap]
      exact hmesh
    have hs := word_slice_value g hfar hbraid w (centers k)
      (uniformTime m hm k.castSucc) (uniformTime m hm k.succ)
      (orderedWordLift_generic_at_odd_grid w hm hodd k.castSucc)
      (orderedWordLift_generic_at_odd_grid w hm hodd k.succ) huv hgap
      (fun t hut htv => hcells k t ⟨hut, htv⟩)
    rw [hvalues i hi]
    have heval : P (i + 1) * (P i)⁻¹ =
        partialWordValue g w (uniformTime m hm k.succ : ℝ) *
          (partialWordValue g w (uniformTime m hm k.castSucc : ℝ))⁻¹ := by
      simp only [P, h0, h1]
    exact hs.trans heval.symm
  have hp0 : P 0 = 1 := by
    simp only [P, gridIndex_zero, uniformTime_zero, Set.Icc.coe_zero, partialWordValue_zero]
  have hpm : P m = wordValue g w := by
    simp only [P, gridIndex_last, uniformTime_last, Set.Icc.coe_one, partialWordValue_one]
  calc
    wordValue g w = P m * (P 0)⁻¹ := by rw [hp0, hpm, inv_one, mul_one]
    _ = edgeProduct (fun i => P (i + 1) * (P i)⁻¹) m := (edgeProduct_potential P m).symm
    _ = edgeProduct bottom m := (edgeProduct_congr bottom _ m he).symm
    _ = 1 := hprod

/-- The genuine geometric converse: a null free word belongs to the normal
closure of the Artin relators, with both relator orientations allowed. -/
theorem geometric_null_implies_presented_null (n : ℕ) (x : FreeGroup (Fin (n - 1)))
    (hx : FreeGroup.lift (halfTwistBraid n) x = 1) :
    PresentedGroup.mk (braidRels n) x = 1 := by
  cases n with
  | zero =>
    clear hx
    have he : x = 1 := by
      induction x using FreeGroup.induction_on with
      | C1 => rfl
      | of i => exact Fin.elim0 i
      | inv_of i _ => exact Fin.elim0 i
      | mul x y hx hy => rw [hx, hy, mul_one]
    rw [he, map_one]
  | succ n =>
    obtain ⟨w, hw, hloop⟩ := null_free_word_has_null_loop x hx
    have h := word_value_of_null_loop artinGenerator artinGenerator_far artinGenerator_braid w hloop
    rw [wordValue_artin, hw] at h
    exact h

theorem geometric_null_signed_trace (n : ℕ) (x : FreeGroup (Fin (n - 1)))
    (hx : FreeGroup.lift (halfTwistBraid n) x = 1) :
    BraidConverseRepair.SignedRelatorTrace (braidRels n) x :=
  (BraidConverseRepair.SignedRelatorTrace.iff_presented_mk_eq_one _ _).mpr
    (geometric_null_implies_presented_null n x hx)

theorem geometric_kernel_le_normalClosure (n : ℕ) :
    MonoidHom.ker (FreeGroup.lift (halfTwistBraid n)) ≤ Subgroup.normalClosure (braidRels n) := by
  intro x hx
  exact PresentedGroup.mk_eq_one_iff.mp (geometric_null_implies_presented_null n x hx)

end BraidConverse
end

/- HalfTwistInjective -/
section
set_option autoImplicit false

open BraidsLinksMCG

namespace TarchaBraids

theorem thm_3_15_half_twist_hom_injective (n : ℕ)
    (f : ArtinBraidGroup n →* GeomBraidGroup n)
    (hf : ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) :
    Function.Injective f := by
  have he : f.comp (PresentedGroup.mk (braidRels n)) = FreeGroup.lift (halfTwistBraid n) := by
    apply FreeGroup.ext_hom
    intro i
    change f (sigma i) = _
    rw [FreeGroup.lift_apply_of]
    exact hf i
  apply (injective_iff_map_eq_one f).mpr
  intro a ha
  obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective (braidRels n) a
  apply BraidConverse.geometric_null_implies_presented_null n x
  have h := DFunLike.congr_fun he x
  exact h.symm.trans ha

end TarchaBraids
end

theorem solution (n : ℕ) (f : BraidsLinksMCG.ArtinBraidGroup n →* BraidsLinksMCG.GeomBraidGroup n)
    (hf : ∀ i : Fin (n - 1), f (BraidsLinksMCG.sigma i) = TarchaBraids.halfTwistBraid n i) :
    Function.Injective f := TarchaBraids.thm_3_15_half_twist_hom_injective n f hf
