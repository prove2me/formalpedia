-- Prove2me | solution 1 for PhilipponMultiplicity.exists_quadratic_local_addition_reembedding
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T16:14:17.154015+00:00
-- url     : https://prove2.me/submissions/c706a8f3-64e3-42a1-ae06-85bd14eaa31a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_quadratic_addition_local_cover
import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h


end MultiProjectiveSpace
end PhilipponMultiplicity
end
end


section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring


end PhilipponMultiplicity
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)


end PhilipponMultiplicity
end
end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

/-- Substituting tuples homogeneous in each source block preserves
multihomogeneity, with the expected linear transformation of degrees. -/
theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

/-- Two projective lifts represent the same point precisely when all their
two-by-two cross products vanish. -/
theorem projectivization_mk_eq_iff_cross {ι : Type*}
    (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔
      ∀ j k, v j * w k = v k * w j := by
  classical
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp heq
    intro j k
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    change w k ≠ 0 at hk
    apply (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr
    refine ⟨v k / w k, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    exact h k j

/-- Regular maps into a multiprojective space have a closed equalizer, even
though the Zariski topology on the target is not Hausdorff. -/
theorem IsRegularAlong.isClosed_equalizer
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g) :
    @IsClosed X (TopologicalSpace.induced e M.zariskiTopology) {x | f x = g x} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hx
  obtain ⟨U, hU, hxU, D, P, hP, hflift⟩ := hf x b
  obtain ⟨V, hV, hxV, E, Q, hQ, hglift⟩ := hg x b
  obtain ⟨hp, hpx⟩ := hflift x hxU
  obtain ⟨hq, hqx⟩ := hglift x hxV
  have hcross : ∃ j k, M.eval (P j * Q k - P k * Q j) (e x) ≠ 0 := by
    by_contra! hn
    apply hb
    rw [← hpx, ← hqx, projectivization_mk_eq_iff_cross]
    intro j k
    simpa only [eval, map_sub, map_mul, sub_eq_zero] using hn j k
  obtain ⟨j, k, hjk⟩ := hcross
  have hhom := ((hP j).mul M (hQ k)).sub M ((hP k).mul M (hQ j))
  let W := U ∩ V ∩ {p | M.eval (P j * Q k - P k * Q j) p ≠ 0}
  have hopen : IsOpen (e ⁻¹' W) :=
    ((hU.inter hV).inter (M.isOpen_basic _ _ hhom)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hxU, hxV⟩, hjk⟩) ?_
  intro y hy heq
  obtain ⟨hpy, hpy'⟩ := hflift y hy.1.1
  obtain ⟨hqy, hqy'⟩ := hglift y hy.1.2
  have hmk := hpy'.trans ((congrFun heq b).trans hqy'.symm)
  have hz := (projectivization_mk_eq_iff_cross _ _ hpy hqy).mp hmk j k
  exact hy.2 (by simpa only [eval, map_sub, map_mul, sub_eq_zero] using hz)

theorem IsRegularAlong.eq_of_dense
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g)
    (A : Set X) (hA : @Dense X (TopologicalSpace.induced e M.zariskiTopology) A)
    (hfg : Set.EqOn f g A) : f = g := by
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  have hh : closure A ⊆ {x | f x = g x} :=
    closure_minimal hfg (hf.isClosed_equalizer M N hg)
  funext x
  exact hh (hA x)

/-- Regular maps are continuous for the actual polynomial Zariski topologies. -/
theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K] {n : ℕ}

def projectiveLeftSlice (a : Projectivization K (Fin (n + 1) → K))
    (p : (projectiveSpace K n).Point) : (projectiveSquare K n).Point :=
  fun b => if b.val = 0 then p (0 : Fin 1) else a

def projectiveLeftSlicePolynomial (a : Projectivization K (Fin (n + 1) → K))
    (v : (projectiveSquare K n).Variable) : (projectiveSpace K n).CoordinateRing :=
  if v.1.val = 0 then X ⟨(0 : Fin 1), v.2⟩ else C (a.rep v.2)

theorem projectiveLeftSlicePolynomial_homogeneous
    (a : Projectivization K (Fin (n + 1) → K)) (v : (projectiveSquare K n).Variable) :
    (projectiveSpace K n).IsHomogeneous (projectiveLeftSlicePolynomial a v)
      (fun _ => if v.1.val = 0 then 1 else 0) := by
  classical
  by_cases hv : v.1.val = 0
  · simp only [projectiveLeftSlicePolynomial, if_pos hv]
    convert (projectiveSpace K n).isHomogeneous_X ⟨(0 : Fin 1), v.2⟩ using 1
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    simp [hi]
  · simpa only [projectiveLeftSlicePolynomial, if_neg hv] using!
      (projectiveSpace K n).isHomogeneous_C (a.rep v.2)

theorem projectiveLeftSlice_eval (a : Projectivization K (Fin (n + 1) → K))
    (P : (projectiveSquare K n).CoordinateRing) (p : (projectiveSpace K n).Point) :
    (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p =
      (projectiveSquare K n).eval P (projectiveLeftSlice a p) := by
  dsimp only [MultiProjectiveSpace.eval]
  rw [← eval_assoc]
  apply congrArg (fun v => MvPolynomial.eval v P)
  funext v
  by_cases hv : v.1.val = 0 <;>
    simp [projectiveLeftSlicePolynomial, projectiveLeftSlice,
      MultiProjectiveSpace.coordinate, hv]

theorem projectiveLeftSlice_continuous (a : Projectivization K (Fin (n + 1) → K)) :
    @Continuous _ _ (projectiveSpace K n).zariskiTopology
      (projectiveSquare K n).zariskiTopology (projectiveLeftSlice a) := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨P, D, hP, rfl⟩
  have heq : projectiveLeftSlice a ⁻¹' {p | (projectiveSquare K n).eval P p ≠ 0} =
      {p | (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0} := by
    ext p
    change (projectiveSquare K n).eval P (projectiveLeftSlice a p) ≠ 0 ↔
      (projectiveSpace K n).eval (eval₂ C (projectiveLeftSlicePolynomial a) P) p ≠ 0
    rw [projectiveLeftSlice_eval]
  rw [heq]
  apply (projectiveSpace K n).isOpen_basic
  exact hP.eval₂_blocks _ _ _ (fun b _ => if b.val = 0 then 1 else 0)
    (projectiveLeftSlicePolynomial_homogeneous a)

/-- Fixing one projective argument of a regular map gives a regular map. -/
theorem MultiProjectiveSpace.IsRegularAlong.of_left_slice
    {X : Type u} (N : MultiProjectiveSpace K)
    (a : Projectivization K (Fin (n + 1) → K))
    {e : X → (projectiveSpace K n).Point} {f : X → N.Point}
    (hf : (projectiveSquare K n).IsRegularAlong N (projectiveLeftSlice a ∘ e) f) :
    (projectiveSpace K n).IsRegularAlong N e f := by
  classical
  let := (projectiveSpace K n).zariskiTopology
  let := (projectiveSquare K n).zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hlift⟩ := hf x b
  refine ⟨projectiveLeftSlice a ⁻¹' U, hU.preimage (projectiveLeftSlice_continuous a),
    hxU, (fun i => ∑ c, D c * (if c.val = 0 then 1 else 0)),
    (fun j => eval₂ C (projectiveLeftSlicePolynomial a) (P j)), ?_, ?_⟩
  · intro j
    exact (hP j).eval₂_blocks _ _ _ (fun c _ => if c.val = 0 then 1 else 0)
      (projectiveLeftSlicePolynomial_homogeneous a)
  · intro y hy
    obtain ⟨hn, heq⟩ := hlift y hy
    simpa only [projectiveLeftSlice_eval, Function.comp_apply] using ⟨hn, heq⟩

/-- The regular group law supplies regular translations. -/
theorem EmbeddedCommutativeGroup.translation_regular
    (G : EmbeddedCommutativeGroup K) (a : G.Point) :
    (projectiveSpace K G.ambientDimension).IsRegularAlong
      (projectiveSpace K G.ambientDimension)
      (fun x : G.Point => fun _ => x.val)
      (fun x => fun _ => (x + a).val) := by
  apply MultiProjectiveSpace.IsRegularAlong.of_left_slice _ a.val
  exact G.addition_regular.comp_domain (fun x : G.Point => (x, a))

end PhilipponMultiplicity
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity

/-- A nonvanishing cover by finite-variable polynomials has a finite subcover,
even on an arbitrary subset of affine coordinate tuples. -/
theorem finite_polynomial_nonzero_cover {K σ X ι : Type*} [Field K] [Finite σ]
    (P : ι → MvPolynomial σ K) (v : X → σ → K)
    (hcover : ∀ x, ∃ i, MvPolynomial.eval (v x) (P i) ≠ 0) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, MvPolynomial.eval (v x) (P i) ≠ 0 := by
  classical
  obtain ⟨s,hs,hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := MvPolynomial σ K) (Set.range P)).mp
      (IsNoetherian.noetherian (Ideal.span (Set.range P)))
  choose ind hind using (fun q : s => hs q.property)
  let t : Finset ι := Finset.univ.image ind
  refine ⟨t,?_⟩
  intro x
  by_contra hx
  push Not at hx
  have hle : Ideal.span (Set.range P) ≤ RingHom.ker (MvPolynomial.eval (v x)) := by
    change Ideal.span (Set.range P) = Ideal.span (s : Set (MvPolynomial σ K)) at hspan
    rw [hspan]
    apply Ideal.span_le.mpr
    intro q hq
    change MvPolynomial.eval (v x) q = 0
    have hi : P (ind ⟨q,hq⟩) = q := hind ⟨q,hq⟩
    rw [← hi]
    exact hx (ind ⟨q,hq⟩) (Finset.mem_image.mpr ⟨⟨q,hq⟩,Finset.mem_univ _,rfl⟩)
  obtain ⟨i,hi⟩ := hcover x
  exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Every open cover of an arbitrary multiprojective locus admits a finite
subcover. This supplies the finite family needed for uniform chart degrees. -/
theorem finite_open_subcover {X ι : Type*} (e : X → M.Point)
    (U : ι → Set M.Point) (hU : ∀ i, @IsOpen _ M.zariskiTopology (U i))
    (hcover : ∀ x, ∃ i, e x ∈ U i) :
    ∃ t : Finset ι, ∀ x, ∃ i ∈ t, e x ∈ U i := by
  classical
  letI : TopologicalSpace M.Point := M.zariskiTopology
  choose ind hind using hcover
  have hbasic (x : X) : ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
      M.eval P (e x) ≠ 0 ∧ {p : M.Point | M.eval P p ≠ 0} ⊆ U (ind x) := by
    obtain ⟨V,⟨P,D,hP,rfl⟩,hx,hV⟩ :=
      M.isTopologicalBasis_basic.exists_subset_of_mem_open (hind x) (hU (ind x))
    exact ⟨P,D,hP,hx,hV⟩
  choose P D hP hx hPU using hbasic
  obtain ⟨s,hs⟩ := finite_polynomial_nonzero_cover P (fun x => M.coordinate (e x))
    (fun x => ⟨x,hx x⟩)
  refine ⟨s.image ind,?_⟩
  intro x
  obtain ⟨y,hy,hyx⟩ := hs x
  exact ⟨ind y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,hPU y hyx⟩

end MultiProjectiveSpace
end PhilipponMultiplicity

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set MvPolynomial TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem noetherian_induced {X : Type*} (e : X → M.Point) :
    @NoetherianSpace X (TopologicalSpace.induced e M.zariskiTopology) := by
  letI : TopologicalSpace M.Point := M.zariskiTopology
  letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
  apply noetherianSpace_iff_isCompact.mpr
  intro S
  apply isCompact_iff_finite_subcover.mpr
  intro ι U hU hcover
  choose W hW heq using fun i => isOpen_induced_iff.mp (hU i)
  obtain ⟨t,ht⟩ := M.finite_open_subcover (fun x : S => e x.val) W hW (by
    intro x
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover x.property)
    exact ⟨i,by change x.val ∈ e ⁻¹' W i; rwa [heq i]⟩)
  refine ⟨t,?_⟩
  intro x hx
  obtain ⟨i,hi,hxi⟩ := ht ⟨x,hx⟩
  exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,by rw [← heq i]; exact hxi⟩⟩

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
noncomputable section

namespace PhilipponMultiplicity

/-- A connected Noetherian space on which homeomorphisms act transitively
is irreducible. This uses only individual homeomorphisms, not a topological
group structure on the Zariski topology. -/
theorem irreducible_of_transitive_homeomorphisms {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [ConnectedSpace X]
    (htrans : ∀ x y : X, ∃ e : X ≃ₜ X, e x = y) : IrreducibleSpace X := by
  classical
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨U,hU,⟨p,hp⟩,hUC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hCopen : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨e,he⟩ := htrans p y
    have hopen : IsOpen (e '' U) := e.isOpenMap _ hU
    have hclosed : IsClosed (e '' C) := e.isClosedMap _
      (isClosed_of_mem_irreducibleComponents C hC)
    have hydense : C ⊆ closure (C ∩ e '' U) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hopen
        ⟨y,hy,p,hp,he⟩
    have hCeC : C ⊆ e '' C := hydense.trans (closure_minimal
      (fun z hz => Set.image_mono hUC hz.2) hclosed)
    have heCC : e '' C ⊆ C := hC.2 (hC.1.image e e.continuous.continuousOn) hCeC
    exact Filter.mem_of_superset (hopen.mem_nhds ⟨p,hp,he⟩)
      ((Set.image_mono hUC).trans heCC)
  have hfull : C = univ := (show IsClopen C from
    ⟨isClosed_of_mem_irreducibleComponents C hC,hCopen⟩).eq_univ hC.1.nonempty
  exact { isPreirreducible_univ := by simpa only [hfull] using hC.1.2
          toNonempty := inferInstance }


end PhilipponMultiplicity
end
end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 60000
open Set TopologicalSpace
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity

/-- Separate continuity suffices for irreducibility of a topology on a
cartesian product. The topology need not be the product topology. -/
theorem preirreducible_of_continuous_slices
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PreirreducibleSpace X] [PreirreducibleSpace Y]
    (t : TopologicalSpace (X × Y))
    (hl : ∀ y, @Continuous X (X × Y) _ t (fun x => (x,y)))
    (hr : ∀ x, @Continuous Y (X × Y) _ t (fun y => (x,y))) :
    @IsPreirreducible (X × Y) t univ := by
  let : TopologicalSpace (X × Y) := t
  intro U V hU hV hUne hVne
  let A : Set X := {x | ∃ y, (x,y) ∈ U}
  let B : Set X := {x | ∃ y, (x,y) ∈ V}
  have hA : IsOpen A := by
    have he : A = ⋃ y, (fun x : X => (x,y)) ⁻¹' U := by ext x; simp [A]
    rw [he]
    exact isOpen_iUnion (fun y => hU.preimage (hl y))
  have hB : IsOpen B := by
    have he : B = ⋃ y, (fun x : X => (x,y)) ⁻¹' V := by ext x; simp [B]
    rw [he]
    exact isOpen_iUnion (fun y => hV.preimage (hl y))
  obtain ⟨a, -, ha⟩ := hUne
  obtain ⟨b, -, hb⟩ := hVne
  obtain ⟨x, -, ⟨y, hy⟩, ⟨z, hz⟩⟩ :=
    PreirreducibleSpace.isPreirreducible_univ A B hA hB
      ⟨a.1, mem_univ _, a.2, ha⟩ ⟨b.1, mem_univ _, b.2, hb⟩
  obtain ⟨w, -, hwU, hwV⟩ :=
    PreirreducibleSpace.isPreirreducible_univ _ _
      (hU.preimage (hr x)) (hV.preimage (hr x))
      ⟨y, mem_univ _, hy⟩ ⟨z, mem_univ _, hz⟩
  exact ⟨(x,w), mem_univ _, hwU, hwV⟩

universe u
variable {K : Type u} [Field K]

abbrev EmbeddedCommutativeGroup.pointZariskiTopology (E : EmbeddedCommutativeGroup K) :
    TopologicalSpace E.Point :=
  TopologicalSpace.induced (fun x : E.Point => fun _ => x.val)
    (projectiveSpace K E.ambientDimension).zariskiTopology

/-- The one-factor product convention has the same connected points as the
underlying embedded group. -/
theorem EmbeddedCommutativeGroup.connectedSpace_of_single
    (E : EmbeddedCommutativeGroup K)
    (hE : @IsConnected _ (singleGroupProduct E).zariskiTopology univ) :
    @ConnectedSpace E.Point E.pointZariskiTopology := by
  let := (singleGroupProduct E).zariskiTopology
  let := E.pointZariskiTopology
  let := (projectiveSpace K E.ambientDimension).zariskiTopology
  let := (singleGroupProduct E).ambient.zariskiTopology
  let : ConnectedSpace (singleGroupProduct E).Point := connectedSpace_iff_univ.mpr hE
  let f : (singleGroupProduct E).Point → E.Point := fun x => x (0 : Fin 1)
  have hc : Continuous f := by
    apply continuous_induced_rng.mpr
    have he : (fun x : (singleGroupProduct E).Point => fun _ => (x (0 : Fin 1)).val) =
        (singleGroupProduct E).embedding := by
      funext x i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      rfl
    change @Continuous (singleGroupProduct E).Point (projectiveSpace K E.ambientDimension).Point
      (singleGroupProduct E).zariskiTopology (projectiveSpace K E.ambientDimension).zariskiTopology
      (fun x => fun _ => (x (0 : Fin 1)).val)
    have hd : @Continuous (singleGroupProduct E).Point (singleGroupProduct E).ambient.Point
        (singleGroupProduct E).zariskiTopology (singleGroupProduct E).ambient.zariskiTopology
        (singleGroupProduct E).embedding := continuous_induced_dom
    exact hd.congr (fun x => (congrFun he x).symm)
  exact (show Function.Surjective f from
    fun x => ⟨fun _ => x, rfl⟩).connectedSpace hc

/-- Connected embedded groups are irreducible by the Noetherian transitive
homeomorphism criterion, using the regular translations already proved. -/
theorem EmbeddedCommutativeGroup.irreducible_of_connected
    (E : EmbeddedCommutativeGroup K)
    (hE : @ConnectedSpace E.Point E.pointZariskiTopology) :
    @IrreducibleSpace E.Point E.pointZariskiTopology := by
  let := E.pointZariskiTopology
  let := (projectiveSpace K E.ambientDimension).zariskiTopology
  let : ConnectedSpace E.Point := hE
  let : NoetherianSpace E.Point :=
    (projectiveSpace K E.ambientDimension).noetherian_induced (fun x : E.Point => fun _ => x.val)
  apply irreducible_of_transitive_homeomorphisms
  intro x y
  have hc (a : E.Point) : Continuous (fun z : E.Point => z+a) :=
    continuous_induced_rng.mpr (E.translation_regular a).continuous
  let e : E.Point ≃ₜ E.Point := {
    toEquiv := {
      toFun := fun z => z+(y-x)
      invFun := fun z => z-(y-x)
      left_inv := fun z => add_sub_cancel_right z (y-x)
      right_inv := fun z => sub_add_cancel z (y-x) }
    continuous_toFun := hc (y-x)
    continuous_invFun := by simpa only [sub_eq_add_neg] using hc (-(y-x)) }
  refine ⟨e, ?_⟩
  change x+(y-x)=y
  abel

/-- Exchanging the two coordinate blocks is regular and hence continuous
for the multiprojective polynomial Zariski topology. -/
theorem projectiveSquare_swap_continuous (n : ℕ) :
    @Continuous _ _ (projectiveSquare K n).zariskiTopology
      (projectiveSquare K n).zariskiTopology
      (fun p : (projectiveSquare K n).Point => fun b : Fin 2 => p b.rev) := by
  let := (projectiveSquare K n).zariskiTopology
  have hr : (projectiveSquare K n).IsRegularAlong (projectiveSquare K n) id
      (fun p => fun b : Fin 2 => p b.rev) := by
    intro p b
    refine ⟨univ, isOpen_univ, mem_univ _,
      (fun i => if i=b.rev then 1 else 0),
      (fun j => MvPolynomial.X ⟨b.rev,j⟩),
      (fun j => (projectiveSquare K n).isHomogeneous_X ⟨b.rev,j⟩), ?_⟩
    intro q _
    simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_X,
      MultiProjectiveSpace.coordinate, id_eq]
    exact ⟨Projectivization.rep_nonzero (q b.rev), Projectivization.mk_rep (q b.rev)⟩
  have hc := hr.continuous
  rw [induced_id] at hc
  exact hc

/-- The pair variety of a connected embedded group is irreducible for the
actual induced multiprojective topology, via continuity of both slices. -/
theorem EmbeddedCommutativeGroup.preirreducible_pairs
    (F : EmbeddedCommutativeGroup K)
    (hF : @ConnectedSpace F.Point F.pointZariskiTopology) :
    @IsPreirreducible (F.Point × F.Point)
      (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
        (projectiveSquare K F.ambientDimension).zariskiTopology) univ := by
  let := F.pointZariskiTopology
  let := (projectiveSpace K F.ambientDimension).zariskiTopology
  let := (projectiveSquare K F.ambientDimension).zariskiTopology
  let : IrreducibleSpace F.Point := F.irreducible_of_connected hF
  have hl (y : F.Point) : Continuous (fun x : F.Point => F.additionPair x y) :=
    (projectiveLeftSlice_continuous y.val).comp
      (show Continuous (show F.Point → (projectiveSpace K F.ambientDimension).Point
        from fun x => fun _ => x.val) from continuous_induced_dom)
  have hr (x : F.Point) : Continuous (fun y : F.Point => F.additionPair x y) := by
    have he : (fun y : F.Point => F.additionPair x y) =
        (fun p : (projectiveSquare K F.ambientDimension).Point => fun b : Fin 2 => p b.rev) ∘
          (fun y : F.Point => F.additionPair y x) := by
      funext y b
      fin_cases b <;> rfl
    rw [he]
    exact (projectiveSquare_swap_continuous F.ambientDimension).comp (hl x)
  apply preirreducible_of_continuous_slices
  · intro y
    exact continuous_induced_rng.mpr (hl y)
  · intro x
    exact continuous_induced_rng.mpr (hr x)

/-- Regular reembedding transfers connectedness, so pair irreducibility
does not need to be assumed as part of the geometric construction. -/
theorem AlgebraicReembedding.preirreducible_pairs
    {E F : EmbeddedCommutativeGroup K} (e : AlgebraicReembedding E F)
    (hE : @IsConnected _ (singleGroupProduct E).zariskiTopology univ) :
    @IsPreirreducible (F.Point × F.Point)
      (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
        (projectiveSquare K F.ambientDimension).zariskiTopology) univ := by
  let := E.pointZariskiTopology
  let := F.pointZariskiTopology
  let := (projectiveSpace K F.ambientDimension).zariskiTopology
  let : ConnectedSpace E.Point := E.connectedSpace_of_single hE
  have hc : Continuous e.equivalence := continuous_induced_rng.mpr e.regular.continuous
  exact F.preirreducible_pairs (e.equivalence.surjective.connectedSpace hc)

end PhilipponMultiplicity

end
end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology

namespace PhilipponMultiplicity

/-- Pair irreducibility follows from connectedness and regular reembedding;
the only geometric input is the covering family of local quadratic formulas. -/
theorem local_quadratic_reembedding_of_cover
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (hgeometry :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ,
          ∃ P : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          D (0 : Fin 2) ≤ 2 ∧
          (∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D) ∧
          ∀ xy ∈ U, ∃ h :
            (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
              (F.additionPair xy.1 xy.2)) ≠ 0,
            Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
              (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val) :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        @IsPreirreducible (F.Point × F.Point)
          (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) Set.univ ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ,
          ∃ P : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          D (0 : Fin 2) ≤ 2 ∧
          (∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D) ∧
          ∀ xy ∈ U, ∃ h :
            (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
              (F.additionPair xy.1 xy.2)) ≠ 0,
            Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
              (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val := by
  intro E hconnected
  obtain ⟨F, ⟨e⟩, hcover⟩ := hgeometry E hconnected
  exact ⟨F, ⟨e⟩, e.preirreducible_pairs hconnected, hcover⟩

end PhilipponMultiplicity

end
end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        @IsPreirreducible (F.Point × F.Point)
          (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) Set.univ ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ,
          ∃ P : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          D (0 : Fin 2) ≤ 2 ∧
          (∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D) ∧
          ∀ xy ∈ U, ∃ h :
            (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
              (F.additionPair xy.1 xy.2)) ≠ 0,
            Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
              (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val := by
  exact local_quadratic_reembedding_of_cover K (exists_quadratic_addition_local_cover K)
