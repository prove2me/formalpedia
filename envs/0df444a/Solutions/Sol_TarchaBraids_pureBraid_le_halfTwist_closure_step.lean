-- Prove2me | solution 1 for TarchaBraids.pureBraid_le_halfTwist_closure_step
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:36:41.912346+00:00
-- url     : https://prove2.me/submissions/04b1fb66-bf74-4f13-875f-73407c0eaaae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_ker_image_le_halfTwist
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

namespace Assembly


variable (n : ℕ)

/-- A real coordinate strictly to the right of every point of the configuration,
which takes the value `n+1` at the base configuration. -/
noncomputable def newRe (p : Fin n → ℂ) : ℝ :=
  (n : ℝ) + 1 + ∑ i, max ((p i).re - (n : ℝ)) 0

lemma newRe_gt (p : Fin n → ℂ) (j : Fin n) : (p j).re < newRe n p := by
  have h1 : ∀ i : Fin n, 0 ≤ max ((p i).re - (n : ℝ)) 0 := fun i => le_max_right _ _
  have h2 : max ((p j).re - (n : ℝ)) 0 ≤ ∑ i, max ((p i).re - (n : ℝ)) 0 :=
    Finset.single_le_sum (fun i _ => h1 i) (Finset.mem_univ j)
  rcases le_or_gt ((p j).re) (n : ℝ) with h | h
  · have hs : (0 : ℝ) ≤ ∑ i, max ((p i).re - (n : ℝ)) 0 :=
      Finset.sum_nonneg (fun i _ => h1 i)
    unfold newRe; linarith
  · have hm : max ((p j).re - (n : ℝ)) 0 = (p j).re - (n : ℝ) := max_eq_left (by linarith)
    rw [hm] at h2
    unfold newRe; linarith

lemma continuous_newRe : Continuous (fun p : OrderedConfig n => newRe n p.1) := by
  unfold newRe
  refine continuous_const.add (continuous_finset_sum _ fun i _ => ?_)
  exact ((Complex.continuous_re.comp ((continuous_apply i).comp continuous_subtype_val)).sub
    continuous_const).max continuous_const

/-- The configuration with one extra point added to the right of all the others. -/
noncomputable def sectFun (p : OrderedConfig n) : Fin (n + 1) → ℂ :=
  Fin.snoc p.1 ((newRe n p.1 : ℝ) : ℂ)

lemma sectFun_injective (p : OrderedConfig n) : Function.Injective (sectFun n p) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast b =>
      exfalso
      rw [sectFun, Fin.snoc_last, Fin.snoc_castSucc] at hij
      have := congrArg Complex.re hij
      simp only [Complex.ofReal_re] at this
      exact absurd this.symm (ne_of_lt (newRe_gt n p.1 b))
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      exfalso
      rw [sectFun, Fin.snoc_castSucc, Fin.snoc_last] at hij
      have := congrArg Complex.re hij
      simp only [Complex.ofReal_re] at this
      exact absurd this (ne_of_lt (newRe_gt n p.1 a))
    | cast b =>
      rw [sectFun, Fin.snoc_castSucc, Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc (p.2 hij)

/-- Adding a strand far to the right, as a continuous map of configuration spaces. -/
noncomputable def sect : C(OrderedConfig n, OrderedConfig (n + 1)) where
  toFun p := ⟨sectFun n p, sectFun_injective n p⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine continuous_pi fun i => ?_
    induction i using Fin.lastCases with
    | last =>
      simp only [sectFun, Fin.snoc_last]
      exact Complex.continuous_ofReal.comp (continuous_newRe n)
    | cast a =>
      simp only [sectFun, Fin.snoc_castSucc]
      exact (continuous_apply a).comp continuous_subtype_val

lemma forget_sect (p : OrderedConfig n) : configForget n (sect n p) = p := by
  apply Subtype.ext
  funext i
  show sectFun n p i.castSucc = p.1 i
  simp [sectFun]

lemma sect_base : sect n (baseOrdered n) = baseOrdered (n + 1) := by
  apply Subtype.ext
  funext i
  induction i using Fin.lastCases with
  | last =>
    show sectFun n (baseOrdered n) (Fin.last n) = (baseOrdered (n + 1)).1 (Fin.last n)
    simp only [sectFun, Fin.snoc_last]
    have hsum : ∑ i : Fin n, max (((baseOrdered n).1 i).re - (n : ℝ)) 0 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hre : ((baseOrdered n).1 i).re = ((i : ℕ) : ℝ) + 1 := by
        show (((i : ℕ) + 1 : ℂ)).re = _
        simp
      rw [hre]
      have : ((i : ℕ) : ℝ) + 1 - (n : ℝ) ≤ 0 := by
        have := i.isLt
        have : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
        linarith
      exact max_eq_right this
    rw [newRe, hsum]
    show ((((n : ℝ) + 1 + 0 : ℝ)) : ℂ) = (((Fin.last n : ℕ) : ℕ) + 1 : ℂ)
    push_cast
    ring
  | cast a =>
    show sectFun n (baseOrdered n) a.castSucc = (baseOrdered (n + 1)).1 a.castSucc
    simp only [sectFun, Fin.snoc_castSucc]
    show (((a : ℕ) + 1 : ℂ)) = (((a.castSucc : ℕ) : ℕ) + 1 : ℂ)
    norm_num

theorem forget_comp_sect :
    (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp
        (FundamentalGroup.mapOfEq (sect n) (sect_base n))
      = MonoidHom.id (PureBraidGroup n) := by
  refine MonoidHom.ext fun γ => ?_
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (FundamentalGroup.toPath γ)
  have hγ : FundamentalGroup.fromPath (⟦Q⟧ : Path.Homotopic.Quotient _ _) = γ :=
    congrArg FundamentalGroup.fromPath hQ
  rw [← hγ]
  show (FundamentalGroup.mapOfEq (configForget n) (configForget_base n))
      ((FundamentalGroup.mapOfEq (sect n) (sect_base n))
        (FundamentalGroup.fromPath (⟦Q⟧ : Path.Homotopic.Quotient _ _)))
    = FundamentalGroup.fromPath (⟦Q⟧ : Path.Homotopic.Quotient _ _)
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  have hpath :
      ((((Q.map (sect n).continuous).cast (sect_base n).symm (sect_base n).symm).map
        (configForget n).continuous).cast (configForget_base n).symm
          (configForget_base n).symm) = Q := by
    refine DFunLike.ext _ _ fun t => ?_
    exact forget_sect n (Q t)
  show (⟦(((Q.map (sect n).continuous).cast (sect_base n).symm (sect_base n).symm).map
        (configForget n).continuous).cast (configForget_base n).symm
          (configForget_base n).symm⟧ : Path.Homotopic.Quotient _ _) = ⟦Q⟧
  rw [hpath]

/-- On a half-twist configuration every point has real part at most `n`. -/
lemma halfTwistFun_re_le (n : ℕ) (i : Fin (n - 1)) (t : ℝ) (k : Fin n) :
    (halfTwistFun n i t k).re ≤ (n : ℝ) := by
  have hi := i.isLt
  have hk := k.isLt
  have hcos : Real.cos (Real.pi * t) ≤ 1 := Real.cos_le_one _
  have hcos' : -1 ≤ Real.cos (Real.pi * t) := Real.neg_one_le_cos _
  have hin : ((i : ℕ) : ℝ) + 2 ≤ (n : ℝ) := by
    have : (i : ℕ) + 2 ≤ n := by omega
    exact_mod_cast this
  unfold halfTwistFun
  split_ifs with h1 h2
  · rw [twistPoint_re]; push_cast; linarith
  · rw [twistPoint_re]; push_cast; linarith
  · simp only [Complex.ofReal_re]
    have : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
      have : (k : ℕ) + 1 ≤ n := by omega
      exact_mod_cast this
    linarith

/-- Hence the adjoined point is exactly `n+1`. -/
lemma newRe_halfTwist (n : ℕ) (i : Fin (n - 1)) (t : ℝ) :
    newRe n (halfTwistConfig n i t).1 = (n : ℝ) + 1 := by
  unfold newRe
  have : ∀ k : Fin n, max (((halfTwistConfig n i t).1 k).re - (n : ℝ)) 0 = 0 := by
    intro k
    refine max_eq_right ?_
    have := halfTwistFun_re_le n i t k
    show ((halfTwistFun n i t k).re - (n : ℝ)) ≤ 0
    linarith
  rw [Finset.sum_congr rfl (fun k _ => this k)]
  simp

/-- Adding a far-right strand carries a half-twist configuration to the half-twist
configuration on one more strand, at the same index. -/
lemma sect_halfTwistConfig (n : ℕ) (i : Fin (n - 1)) (t : ℝ) :
    sect n (halfTwistConfig n i t)
      = halfTwistConfig (n + 1) (Fin.castLE (by omega) i) t := by
  have hi := i.isLt
  apply Subtype.ext
  funext k
  show sectFun n (halfTwistConfig n i t) k
    = halfTwistFun (n + 1) (Fin.castLE (by omega) i) t k
  induction k using Fin.lastCases with
  | last =>
    simp only [sectFun, Fin.snoc_last]
    rw [newRe_halfTwist]
    unfold halfTwistFun
    rw [if_neg, if_neg]
    · push_cast; ring
    · simp only [Fin.val_last, Fin.coe_castLE]; omega
    · simp only [Fin.val_last, Fin.coe_castLE]; omega
  | cast a =>
    simp only [sectFun, Fin.snoc_castSucc]
    show halfTwistFun n i t a = _
    unfold halfTwistFun
    simp only [Fin.coe_castSucc, Fin.coe_castLE]

/-- Extend a permutation of `Fin n` to `Fin (n+1)` by fixing the last index. -/
def extPerm {n : ℕ} (g : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.lastCases (Fin.last n) (fun a => (g a).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun a => (g.symm a).castSucc)
  left_inv := by
    intro x
    induction x using Fin.lastCases with
    | last => simp
    | cast a => simp
  right_inv := by
    intro x
    induction x using Fin.lastCases with
    | last => simp
    | cast a => simp

/-- The adjoined coordinate depends only on the unordered configuration. -/
lemma newRe_comp (n : ℕ) (p : Fin n → ℂ) (g : Equiv.Perm (Fin n)) :
    newRe n (p ∘ g) = newRe n p := by
  unfold newRe
  congr 1
  exact Fintype.sum_equiv g _ _ (fun i => rfl)

/-- Adding a far-right strand respects relabelling, so it descends to unordered
configurations. -/
lemma sect_congr (n : ℕ) (p q : OrderedConfig n) (h : (configSetoid n).r p q) :
    (configSetoid (n + 1)).r (sect n p) (sect n q) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨extPerm g, ?_⟩
  funext x
  induction x using Fin.lastCases with
  | last =>
    show sectFun n q (Fin.last n) = sectFun n p (extPerm g (Fin.last n))
    simp only [extPerm, Equiv.coe_fn_mk, Fin.lastCases_last, sectFun, Fin.snoc_last]
    rw [hg, newRe_comp]
  | cast a =>
    show sectFun n q a.castSucc = sectFun n p (extPerm g a.castSucc)
    simp only [extPerm, Equiv.coe_fn_mk, Fin.lastCases_castSucc, sectFun, Fin.snoc_castSucc]
    rw [hg]
    rfl

/-- Adding a far-right strand, as a map of unordered configuration spaces. -/
noncomputable def addU (n : ℕ) : C(UnorderedConfig n, UnorderedConfig (n + 1)) where
  toFun := Quotient.lift (fun p => configProj (n + 1) (sect n p))
    (fun p q h => Quotient.sound (sect_congr n p q h))
  continuous_toFun := by
    apply continuous_quot_lift
    exact (configProj (n + 1)).continuous.comp (sect n).continuous

@[simp] lemma addU_mk (n : ℕ) (p : OrderedConfig n) :
    addU n (configProj n p) = configProj (n + 1) (sect n p) := rfl

lemma addU_base (n : ℕ) : addU n (baseUnordered n) = baseUnordered (n + 1) := by
  show configProj (n + 1) (sect n (baseOrdered n)) = _
  rw [sect_base]
  rfl

/-- Adding a far-right strand sends each elementary half-twist to the elementary
half-twist of the same index on one more strand. -/
theorem addU_halfTwist (n : ℕ) (i : Fin (n - 1)) :
    FundamentalGroup.mapOfEq (addU n) (addU_base n) (halfTwistBraid n i)
      = halfTwistBraid (n + 1) (Fin.castLE (by omega) i) := by
  have hpath :
      ((halfTwistLoop n i).map (addU n).continuous).cast (addU_base n).symm (addU_base n).symm
        = halfTwistLoop (n + 1) (Fin.castLE (by omega) i) := by
    refine DFunLike.ext _ _ fun t => ?_
    show addU n (configProj n (halfTwistConfig n i (t : ℝ))) = _
    rw [addU_mk, sect_halfTwistConfig]
    rfl
  rw [FundamentalGroup.mapOfEq_apply]
  show FundamentalGroup.fromPath
      ((⟦((halfTwistLoop n i).map (addU n).continuous).cast (addU_base n).symm
          (addU_base n).symm⟧) : Path.Homotopic.Quotient _ _) = _
  rw [hpath]
  rfl

/-- A split surjection expresses the source as the kernel together with the image
of the section. -/
theorem pureBraid_ker_sup_section (n : ℕ)
    (s : PureBraidGroup n →* PureBraidGroup (n + 1))
    (hs : (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
        MonoidHom.id (PureBraidGroup n)) :
    (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker ⊔ s.range = ⊤ := by
  rw [eq_top_iff]
  intro x _
  set p := FundamentalGroup.mapOfEq (configForget n) (configForget_base n) with hp
  have hps : ∀ w : PureBraidGroup n, p (s w) = w := fun w => DFunLike.congr_fun hs w
  have h1 : x * (s (p x))⁻¹ ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hps, mul_inv_cancel]
  have h2 : s (p x) ∈ s.range := ⟨p x, rfl⟩
  have h3 : x = (x * (s (p x))⁻¹) * s (p x) := by group
  rw [h3]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)


/-- Functoriality of the base-point-cast induced map. Not in Mathlib. -/
lemma mapOfEq_comp {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (h1 : f x = y) (h2 : g y = z) :
    (FundamentalGroup.mapOfEq g h2).comp (FundamentalGroup.mapOfEq f h1)
      = FundamentalGroup.mapOfEq (g.comp f)
          (show (g.comp f) x = z by simp only [ContinuousMap.comp_apply, h1, h2]) := by
  subst h1
  subst h2
  refine MonoidHom.ext fun p => ?_
  rw [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  induction p using Quotient.ind with
  | _ P => rfl

/-- The cast form of the induced map agrees with the plain one along `rfl`. -/
lemma mapOfEq_rfl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  refine MonoidHom.ext fun p => ?_
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

/-- The square: projecting after adding a strand equals adding a strand after
projecting. The two composite continuous maps are *the same map*, so this is
functoriality applied twice. -/
lemma proj_comp_sect (n : ℕ)
    (hA : configProj (n + 1) (baseOrdered (n + 1)) = baseUnordered (n + 1))
    (hB : configProj n (baseOrdered n) = baseUnordered n) :
    (FundamentalGroup.mapOfEq (configProj (n + 1)) hA).comp
        (FundamentalGroup.mapOfEq (sect n) (sect_base n))
      = (FundamentalGroup.mapOfEq (addU n) (addU_base n)).comp
        (FundamentalGroup.mapOfEq (configProj n) hB) :=
  (mapOfEq_comp (sect n) (configProj (n + 1)) (sect_base n) hA).trans
    (mapOfEq_comp (configProj n) (addU n) hB (addU_base n)).symm

end Assembly

open Assembly

theorem _root_.solution (n : ℕ)
    (ih : (FundamentalGroup.map (configProj n) (baseOrdered n)).range ≤
      Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i))) :
    (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1))).range ≤
      Subgroup.closure
        (Set.range (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)) := by
  have hskel := pureBraid_ker_sup_section n
    (FundamentalGroup.mapOfEq (sect n) (sect_base n)) (forget_comp_sect n)
  -- the square, transported to the cast-free form of the projections
  have hsq : (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1))).comp
        (FundamentalGroup.mapOfEq (sect n) (sect_base n))
      = (FundamentalGroup.mapOfEq (addU n) (addU_base n)).comp
        (FundamentalGroup.map (configProj n) (baseOrdered n)) := by
    rw [← mapOfEq_rfl (configProj (n + 1)) (baseOrdered (n + 1)),
      ← mapOfEq_rfl (configProj n) (baseOrdered n)]
    exact proj_comp_sect n rfl rfl
  -- adding a strand carries the half-twist subgroup into the next one
  have hH : Subgroup.map (FundamentalGroup.mapOfEq (addU n) (addU_base n))
      (Subgroup.closure (Set.range (fun i : Fin (n - 1) => halfTwistBraid n i)))
      ≤ Subgroup.closure
        (Set.range (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)) := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨z, ⟨i, rfl⟩, rfl⟩
    rw [addU_halfTwist]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  rw [MonoidHom.range_eq_map, ← hskel, Subgroup.map_sup]
  refine sup_le (BraidsLinksMCG.fadellNeuwirth_ker_image_le_halfTwist n) ?_
  have key : Subgroup.map (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
        (FundamentalGroup.mapOfEq (sect n) (sect_base n)).range
      = Subgroup.map (FundamentalGroup.mapOfEq (addU n) (addU_base n))
        (FundamentalGroup.map (configProj n) (baseOrdered n)).range := by
    rw [MonoidHom.range_eq_map (FundamentalGroup.mapOfEq (sect n) (sect_base n)),
      MonoidHom.range_eq_map (FundamentalGroup.map (configProj n) (baseOrdered n))]
    exact (Subgroup.map_map _ _ _).trans
      ((congrArg (fun F => Subgroup.map F (⊤ : Subgroup (PureBraidGroup n))) hsq).trans
        (Subgroup.map_map _ _ _).symm)
  rw [key]
  exact le_trans (Subgroup.map_mono ih) hH

#print axioms solution
