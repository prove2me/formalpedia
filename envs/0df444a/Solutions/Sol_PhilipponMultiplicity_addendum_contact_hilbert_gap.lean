-- Prove2me | solution 1 for PhilipponMultiplicity.addendum_contact_hilbert_gap
-- status  : ACCEPTED   (disprove)
-- author  : @tomasz
-- created : 2026-10-10T13:20:08.962898+00:00
-- url     : https://prove2.me/submissions/7f064f1f-bf78-4cca-9aab-e87500362b84

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_SectionThree
import Definitions.Def_PhilipponMultiplicity_Support
import Mathlib
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic

section
-- Implementation: Solutions.PhilipponProjectiveGeometry

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

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

end MultiProjectiveSpace

theorem singleBlock_isHomogeneous {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    (projectiveSpace K N).IsHomogeneous
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => d) := by
  classical
  intro a ha i
  have h := hP.rename_isHomogeneous (f := fun j => (⟨(0 : Fin 1), j⟩ :
    (projectiveSpace K N).Variable)) (MvPolynomial.mem_support_iff.mp ha)
  change Finsupp.weight (1 : (projectiveSpace K N).Variable → ℕ) a = d at h
  rw [Finsupp.weight_eq_sum] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma] at h
  change (∑ x : Fin 1, ∑ y : Fin (N + 1), a ⟨x, y⟩) = d at h
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ j : Fin (N + 1), a ⟨(0 : Fin 1), j⟩) = d
  exact (Fin.sum_univ_one _).symm.trans h

theorem projective_isOpen_coordinate {K : Type*} [Field K] {N : ℕ}
    (j : Fin (N + 1)) :
    @IsOpen _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | p.rep j ≠ 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isOpen_basic _ _
    (singleBlock_isHomogeneous (MvPolynomial.isHomogeneous_X K j))).preimage
      hcont
  convert h using 1
  ext p
  change p.rep j ≠ 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) (MvPolynomial.X j)) (fun _ => p) ≠ 0
  simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate]

theorem projective_regular_of_homogeneous
    {K X : Type u} [Field K] {N N' d : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K)
    (hP : ∀ j, (P j).IsHomogeneous d)
    (hf : ∀ x, ∃ h : (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval (e x).rep (P j)) h = f x) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => d,
    Q,
    (fun j => singleBlock_isHomogeneous (hP j)), ?_⟩
  intro y _
  have heq : (fun j => (projectiveSpace K N).eval (Q j) (fun _ => e y)) =
      (fun j => MvPolynomial.eval (e y).rep (P j)) := by
    ext j
    change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
    rw [MvPolynomial.eval_rename]
    rfl
  obtain ⟨hne, hmk⟩ := hf y
  change ∃ h : (fun j : Fin (N' + 1) =>
      (projectiveSpace K N).eval (Q j) (fun _ => e y)) ≠ 0,
    Projectivization.mk K
      (fun j : Fin (N' + 1) => (projectiveSpace K N).eval (Q j) (fun _ => e y)) h = f y
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hne
  · simpa only [heq] using hmk

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

end WeierstrassEllipticZeta
end
end

section
-- Implementation: Solutions.PhilipponHomogeneousOperations

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

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

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
-- Implementation: Solutions.PhilipponAnalyticUnitOrder

set_option autoImplicit false
open scoped Topology BigOperators ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

def jetOrder (f : E → K) (x : E) : WithTop ℕ :=
  sInf ((fun n : ℕ => (n : WithTop ℕ)) '' {n | iteratedFDeriv K n f x ≠ 0})

theorem natCast_le_jetOrder_iff {f : E → K} {x : E} {n : ℕ} :
    (n : WithTop ℕ) ≤ jetOrder f x ↔
      ∀ i < n, iteratedFDeriv K i f x = 0 := by
  constructor
  · intro h i hi
    by_contra hne
    have hle : jetOrder f x ≤ (i : WithTop ℕ) := sInf_le ⟨i, hne, rfl⟩
    have : n ≤ i := by exact_mod_cast h.trans hle
    omega
  · intro h
    apply le_sInf
    rintro _ ⟨i, hi, rfl⟩
    by_contra! hlt
    have hin : i < n := by exact_mod_cast hlt
    exact hi (h i hin)

end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions.PhilipponProjectiveContact

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
-- Implementation: Solutions.PhilipponAnalyticContainment

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_lift_eq_zero_of_mem_vanishingIdeal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    {V : Set M.Point} {p : M.Point} (hp : p ∈ V)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal V) :
    MvPolynomial.eval v P = 0 := by
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
  have hideal : M.vanishingIdeal V ≤ RingHom.ker (MvPolynomial.eval v) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hz⟩
    change MvPolynomial.eval v Q = 0
    rw [hv', M.eval_block_scale Q D hD (M.coordinate p) (fun i => (a i : K)),
      show MvPolynomial.eval (M.coordinate p) Q = 0
      from hz p hp, mul_zero]
  exact hideal hP

end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions.PhilipponAdditiveSubgroups

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
-- Implementation: Solutions.PhilipponRegularMapTopology

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
-- Implementation: Solutions.PhilipponRegularMapComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem homogeneous_tuple_lift {ι : Type*} (M : MultiProjectiveSpace K)
    (p : M.Point) (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) D)
    (hn : (fun j => M.eval (P j) p) ≠ 0) :
    ∃ h : (fun j => MvPolynomial.eval v (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval v (P j)) h =
        Projectivization.mk K (fun j => M.eval (P j) p) hn := by
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
  let b : K := ∏ i, (a i : K) ^ D i
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (a i).ne_zero)
  have heval : (fun j => MvPolynomial.eval v (P j)) = b • (fun j => M.eval (P j) p) := by
    funext j
    rw [hv', M.eval_block_scale (P j) D (hP j) (M.coordinate p) (fun i => (a i : K))]
    rfl
  have hn' : (fun j => MvPolynomial.eval v (P j)) ≠ 0 := by
    rw [heval]
    exact smul_ne_zero hb hn
  exact ⟨hn', (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨b, heval.symm⟩⟩

theorem IsRegularAlong.comp {X : Type u} {M N Q : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} {g : X → Q.Point}
    (hf : M.IsRegularAlong N e f) (hg : N.IsRegularAlong Q f g) :
    M.IsRegularAlong Q e g := by
  classical
  let := M.zariskiTopology
  let := N.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  intro x b
  obtain ⟨U, hU, hxU, D, P, hP, hPlift⟩ := hg x b
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp (hU.preimage hf.continuous)
  choose W hW hxW E R hR hRlift using hf x
  let pull (j : Fin (Q.ambientDimension b + 1)) :=
    eval₂ C (fun t : N.Variable => R t.1 t.2) (P j)
  refine ⟨V ∩ ⋂ a, W a, hV.inter (isOpen_iInter_of_finite hW),
    ⟨?_, mem_iInter.mpr hxW⟩, (fun i => ∑ a, D a * E a i), pull, ?_, ?_⟩
  · have hx : x ∈ f ⁻¹' U := hxU
    rwa [← hVeq] at hx
  · intro j
    exact (hP j).eval₂_blocks M N _ E (fun t => hR t.1 t.2)
  · intro y hy
    have hyU : f y ∈ U := by
      change y ∈ f ⁻¹' U
      rw [← hVeq]
      exact hy.1
    obtain ⟨hn, heq⟩ := hPlift y hyU
    have hlift (a : N.FactorIndex) := hRlift a y (mem_iInter.mp hy.2 a)
    obtain ⟨hn', heq'⟩ := N.homogeneous_tuple_lift (f y)
      (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) hlift P D hP hn
    have heval (j) : M.eval (pull j) (e y) =
        MvPolynomial.eval (fun t : N.Variable => M.eval (R t.1 t.2) (e y)) (P j) := by
      dsimp only [eval, pull]
      rw [← eval_assoc]
      rfl
    simpa only [heval] using ⟨hn', heq'.trans heq⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end
end

section
-- Implementation: Solutions.PhilipponAffineAdditiveGroup

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AffineModel
universe u
variable (K : Type u) [Field K] (n : ℕ)

def carrier : Set (Projectivization K (Fin (n+1) → K)) := {p | p.rep 0 ≠ 0}

def point (z : Fin n → K) : Projectivization K (Fin (n+1) → K) :=
  Projectivization.mk K (Fin.cons 1 z) (by
    intro h
    have := congrFun h 0
    simpa using this)

theorem point_mem (z : Fin n → K) : point K n z ∈ carrier K n := by
  have hn : (Fin.cons 1 z : Fin (n+1) → K) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K
    (Fin.cons 1 z : Fin (n+1) → K) hn
  change (Projectivization.mk K (Fin.cons 1 z : Fin (n+1) → K) _).rep 0 ≠ 0
  rw [← hc]
  simpa [Units.smul_def] using c.ne_zero

def coordinateEquiv : carrier K n ≃ (Fin n → K) where
  toFun p j := p.val.rep j.succ / p.val.rep 0
  invFun z := ⟨point K n z,point_mem K n z⟩
  left_inv p := by
    apply Subtype.ext
    apply Eq.trans ?_ p.val.mk_rep
    apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
    refine ⟨(p.val.rep 0)⁻¹,?_⟩
    have hp0 : p.val.rep 0 ≠ 0 := p.property
    ext j
    cases j using Fin.cases <;> simp [hp0,div_eq_mul_inv,mul_comm]
  right_inv z := by
    have hn : (Fin.cons 1 z : Fin (n+1) → K) ≠ 0 := by
      intro h
      exact one_ne_zero (congrFun h 0)
    obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K
      (Fin.cons 1 z : Fin (n+1) → K) hn
    funext j
    change (Projectivization.mk K (Fin.cons 1 z : Fin (n+1) → K) _).rep j.succ /
      (Projectivization.mk K (Fin.cons 1 z : Fin (n+1) → K) _).rep 0 = z j
    rw [← hc]
    simp [Units.smul_def,c.ne_zero]

theorem point_eq_mk {v : Fin (n+1) → K} (hv : v 0 ≠ 0) :
    point K n (fun j => v j.succ / v 0) =
      Projectivization.mk K v (by intro h; exact hv (congrFun h 0)) := by
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨(v 0)⁻¹,?_⟩
  ext j
  cases j using Fin.cases <;> simp [hv,div_eq_mul_inv,mul_comm]

def carrierGroup : AddCommGroup (carrier K n) := (coordinateEquiv K n).addCommGroup

theorem locallyClosed :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p : Projectivization K (Fin (n+1) → K) =>
        (fun _ => p : (projectiveSpace K n).Point))
        (projectiveSpace K n).zariskiTopology) (carrier K n) := by
  letI := TopologicalSpace.induced
    (fun p : Projectivization K (Fin (n+1) → K) =>
      (fun _ => p : (projectiveSpace K n).Point)) (projectiveSpace K n).zariskiTopology
  exact (projective_isOpen_coordinate (K := K) (0 : Fin (n+1))).isLocallyClosed

theorem negation_regular :
    letI := carrierGroup K n
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K n) (projectiveSpace K n)
      (fun x : carrier K n => fun _ => x.val)
      (fun x : carrier K n => fun _ => (-x).val) := by
  letI := carrierGroup K n
  let P : Fin (n+1) → MvPolynomial (Fin (n+1)) K :=
    Fin.cons (X 0) (fun j => -X j.succ)
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    cases j using Fin.cases
    · exact MvPolynomial.isHomogeneous_X K 0
    · exact (MvPolynomial.isHomogeneous_X K _).neg
  · intro x
    let v : Fin (n+1) → K := Fin.cons (x.val.rep 0) (fun j => -x.val.rep j.succ)
    have hv : v 0 ≠ 0 := x.property
    have he : (fun j => MvPolynomial.eval x.val.rep (P j)) = v := by
      funext j
      cases j using Fin.cases <;> simp [P,v]
    refine ⟨by rw [he]; intro h; exact hv (congrFun h 0),?_⟩
    change Projectivization.mk K _ _ =
      point K n (fun j => -(x.val.rep j.succ / x.val.rep 0))
    simpa only [he,v,Fin.cons_succ,Fin.cons_zero,neg_div]
      using (point_eq_mk K n hv).symm

private theorem PhilipponAffineAdditiveGroup_bilinear_homogeneous (a b : Fin (n+1)) :
    (projectiveSquare K n).IsHomogeneous
      (X ⟨(0 : Fin 2),a⟩ * X ⟨(1 : Fin 2),b⟩) (fun _ => 1) := by
  have h := ((projectiveSquare K n).isHomogeneous_X ⟨(0 : Fin 2),a⟩).mul _
    ((projectiveSquare K n).isHomogeneous_X ⟨(1 : Fin 2),b⟩)
  convert h using 1
  funext i
  fin_cases i <;> rfl

theorem addition_regular :
    letI := carrierGroup K n
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare K n) (projectiveSpace K n)
      (fun xy : carrier K n × carrier K n =>
        fun i => if i.val = 0 then xy.1.val else xy.2.val)
      (fun xy : carrier K n × carrier K n => fun _ => (xy.1+xy.2).val) := by
  letI := carrierGroup K n
  letI := (projectiveSquare K n).zariskiTopology
  let P : Fin (n+1) → (projectiveSquare K n).CoordinateRing :=
    Fin.cons (X ⟨(0 : Fin 2),0⟩ * X ⟨(1 : Fin 2),0⟩)
      (fun j => X ⟨(0 : Fin 2),j.succ⟩ * X ⟨(1 : Fin 2),0⟩ +
        X ⟨(0 : Fin 2),0⟩ * X ⟨(1 : Fin 2),j.succ⟩)
  intro x b
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ _,fun _ => 1,P,?_,?_⟩
  · intro j
    cases j using Fin.cases
    · exact PhilipponAffineAdditiveGroup_bilinear_homogeneous K n 0 0
    · exact (PhilipponAffineAdditiveGroup_bilinear_homogeneous K n _ 0).add _ (PhilipponAffineAdditiveGroup_bilinear_homogeneous K n 0 _)
  · intro y _
    let v : Fin (n+1) → K := Fin.cons (y.1.val.rep 0*y.2.val.rep 0)
      (fun j => y.1.val.rep j.succ*y.2.val.rep 0+y.1.val.rep 0*y.2.val.rep j.succ)
    have hv : v 0 ≠ 0 := mul_ne_zero y.1.property y.2.property
    have he : (fun j : Fin (n+1) => (projectiveSquare K n).eval (P j)
        (fun i => if i.val = 0 then y.1.val else y.2.val)) = v := by
      funext j
      cases j using Fin.cases <;>
        simp [P,v,MultiProjectiveSpace.eval,MultiProjectiveSpace.coordinate,projectiveSquare]
    change ∃ h : (fun j : Fin (n+1) => (projectiveSquare K n).eval (P j)
        (fun i => if i.val = 0 then y.1.val else y.2.val)) ≠ 0,
      Projectivization.mk K _ h = (y.1+y.2).val
    refine ⟨by rw [he]; intro h; exact hv (congrFun h 0),?_⟩
    change Projectivization.mk K _ _ = point K n
      (fun j => y.1.val.rep j.succ/y.1.val.rep 0+y.2.val.rep j.succ/y.2.val.rep 0)
    have hs (j : Fin n) : v j.succ/v 0 =
        y.1.val.rep j.succ/y.1.val.rep 0+y.2.val.rep j.succ/y.2.val.rep 0 := by
      exact (div_add_div _ _ y.1.property y.2.property).symm
    simpa only [he,hs] using (point_eq_mk K n hv).symm

end PhilipponMultiplicity.AffineModel

end
end

section
-- Implementation: Solutions.PhilipponProductRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open Set MvPolynomial
open scoped Topology

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

theorem MultiProjectiveSpace.projection_regular (M : MultiProjectiveSpace K)
    (i : M.FactorIndex) :
    M.IsRegularAlong (projectiveSpace K (M.ambientDimension i)) id (fun p _ => p i) := by
  let := M.zariskiTopology
  intro x b
  refine ⟨univ, isOpen_univ, mem_univ _, (fun a => if a = i then 1 else 0),
    (fun j => X ⟨i, j⟩), (fun j => M.isHomogeneous_X ⟨i, j⟩), ?_⟩
  intro y _
  simp only [MultiProjectiveSpace.eval, eval_X, MultiProjectiveSpace.coordinate, id_eq]
  exact ⟨Projectivization.rep_nonzero (y i), Projectivization.mk_rep (y i)⟩

end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions.PhilipponAffineShear

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.AffineModel
universe u
variable (K : Type u) [Field K]

def shear (m : ℕ) (s : K) : (Fin 3 → K) ≃ (Fin 3 → K) where
  toFun z := ![z 0,z 1,z 2+s*z 0^m*z 1]
  invFun z := ![z 0,z 1,z 2-s*z 0^m*z 1]
  left_inv z := by ext j; fin_cases j <;> simp
  right_inv z := by ext j; fin_cases j <;> simp

theorem shear_symm (m : ℕ) (s : K) : (shear K m s).symm = shear K m (-s) := by
  ext z j
  fin_cases j <;> simp [shear,sub_eq_add_neg]

def carrierShear (m : ℕ) (s : K) : carrier K 3 ≃ carrier K 3 :=
  ((coordinateEquiv K 3).trans (shear K m s)).trans (coordinateEquiv K 3).symm

@[simp] theorem carrierShear_coordinates (m : ℕ) (s : K) (p : carrier K 3) :
    coordinateEquiv K 3 (carrierShear K m s p) = shear K m s (coordinateEquiv K 3 p) :=
  (coordinateEquiv K 3).apply_symm_apply _

theorem carrierShear_regular (m : ℕ) (s : K) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K 3) (projectiveSpace K 3)
      (fun p : carrier K 3 => fun _ => p.val)
      (fun p : carrier K 3 => fun _ => (carrierShear K m s p).val) := by
  let P : Fin 4 → MvPolynomial (Fin 4) K :=
    ![X 0^(m+1),X 1*X 0^m,X 2*X 0^m,X 3*X 0^m+C s*X 1^m*X 2]
  apply projective_regular_of_homogeneous _ _ P (d := m+1)
  · intro j
    have hp (i : Fin 4) : (X (R := K) i*X 0^m).IsHomogeneous (m+1) := by
      simpa only [Nat.add_comm] using
        (MvPolynomial.isHomogeneous_X K i).mul (MvPolynomial.isHomogeneous_X_pow 0 m)
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X_pow 0 (m+1)
    · exact hp 1
    · exact hp 2
    · exact (hp 3).add (((MvPolynomial.isHomogeneous_X_pow 1 m).C_mul s).mul
        (MvPolynomial.isHomogeneous_X K 2))
  · intro p
    have hp : p.val.rep 0 ≠ 0 := p.property
    let v : Fin 4 → K := fun j => MvPolynomial.eval p.val.rep (P j)
    have hv : v 0 ≠ 0 := by
      simpa [v,P] using pow_ne_zero (m+1) p.property
    have hr : (fun j : Fin 3 => v j.succ/v 0) =
        shear K m s (coordinateEquiv K 3 p) := by
      funext j
      fin_cases j <;> simp [v,P,shear,coordinateEquiv,pow_succ,div_pow] <;>
        field_simp [hp] <;> ring
    refine ⟨by intro h; exact hv (congrFun h 0),?_⟩
    change Projectivization.mk K v _ = point K 3
      (shear K m s (coordinateEquiv K 3 p))
    rw [← hr]
    exact (point_eq_mk K 3 hv).symm

theorem pairMap_regular {n : ℕ} (f : carrier K n → carrier K n)
    (hf : MultiProjectiveSpace.IsRegularAlong (projectiveSpace K n) (projectiveSpace K n)
      (fun p : carrier K n => fun _ => p.val)
      (fun p : carrier K n => fun _ => (f p).val)) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare K n) (projectiveSquare K n)
      (fun xy : carrier K n × carrier K n =>
        fun i => if i.val = 0 then xy.1.val else xy.2.val)
      (fun xy : carrier K n × carrier K n =>
        fun i => if i.val = 0 then (f xy.1).val else (f xy.2).val) := by
  let pair := fun xy : carrier K n × carrier K n =>
    (fun i : Fin 2 => if i.val = 0 then xy.1.val else xy.2.val)
  have h₀ := ((projectiveSquare K n).projection_regular (0 : Fin 2)).comp_domain pair
  have h₁ := ((projectiveSquare K n).projection_regular (1 : Fin 2)).comp_domain pair
  have hf₀ := hf.comp_domain (fun xy : carrier K n × carrier K n => xy.1)
  have hf₁ := hf.comp_domain (fun xy : carrier K n × carrier K n => xy.2)
  intro x b
  fin_cases b
  · exact (h₀.comp hf₀) x (0 : Fin 1)
  · exact (h₁.comp hf₁) x (0 : Fin 1)

end PhilipponMultiplicity.AffineModel

end
end

section
-- Implementation: Solutions.PhilipponTwistedAffineGroup

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.AffineModel
universe u
variable (K : Type u) [Field K]

def ordinaryAdd (p q : carrier K 3) : carrier K 3 :=
  (coordinateEquiv K 3).symm (coordinateEquiv K 3 p+coordinateEquiv K 3 q)

def ordinaryNeg (p : carrier K 3) : carrier K 3 :=
  (coordinateEquiv K 3).symm (-coordinateEquiv K 3 p)

def untwist (m : ℕ) : carrier K 3 ≃ (Fin 3 → K) :=
  (coordinateEquiv K 3).trans (shear K m 1).symm

def twistedGroup (m : ℕ) : AddCommGroup (carrier K 3) := (untwist K m).addCommGroup

def twistedSum (m : ℕ) (p q : carrier K 3) : carrier K 3 :=
  (untwist K m).symm (untwist K m p+untwist K m q)

def twistedNeg (m : ℕ) (p : carrier K 3) : carrier K 3 :=
  (untwist K m).symm (-untwist K m p)

theorem twistedSum_formula (m : ℕ) (p q : carrier K 3) :
    twistedSum K m p q = carrierShear K m 1
      (ordinaryAdd K (carrierShear K m (-1) p) (carrierShear K m (-1) q)) := by
  apply (coordinateEquiv K 3).injective
  simp only [twistedSum,untwist,Equiv.symm_trans_apply,Equiv.trans_apply,
    Equiv.apply_symm_apply,carrierShear_coordinates,ordinaryAdd,shear_symm,neg_neg]

theorem twistedNeg_formula (m : ℕ) (p : carrier K 3) :
    twistedNeg K m p = carrierShear K m 1
      (ordinaryNeg K (carrierShear K m (-1) p)) := by
  apply (coordinateEquiv K 3).injective
  simp only [twistedNeg,untwist,Equiv.symm_trans_apply,Equiv.trans_apply,
    Equiv.apply_symm_apply,carrierShear_coordinates,ordinaryNeg,shear_symm,neg_neg]

theorem twisted_addition_regular (m : ℕ) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare K 3) (projectiveSpace K 3)
      (fun xy : carrier K 3 × carrier K 3 =>
        fun i => if i.val = 0 then xy.1.val else xy.2.val)
      (fun xy : carrier K 3 × carrier K 3 => fun _ => (twistedSum K m xy.1 xy.2).val) := by
  let back := carrierShear K m (-1)
  have hb := pairMap_regular K back (carrierShear_regular K m (-1))
  have ha := (addition_regular K 3).comp_domain
    (fun xy : carrier K 3 × carrier K 3 => (back xy.1,back xy.2))
  have hf := (carrierShear_regular K m 1).comp_domain
    (fun xy : carrier K 3 × carrier K 3 => ordinaryAdd K (back xy.1) (back xy.2))
  have h := (hb.comp ha).comp hf
  simpa only [Function.comp_def,back,twistedSum_formula] using h

theorem twisted_negation_regular (m : ℕ) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K 3) (projectiveSpace K 3)
      (fun p : carrier K 3 => fun _ => p.val)
      (fun p : carrier K 3 => fun _ => (twistedNeg K m p).val) := by
  let back := carrierShear K m (-1)
  have hb := carrierShear_regular K m (-1)
  have hn := (negation_regular K 3).comp_domain back
  have hf := (carrierShear_regular K m 1).comp_domain
    (fun p : carrier K 3 => ordinaryNeg K (back p))
  have h := (hb.comp hn).comp hf
  simpa only [Function.comp_def,back,twistedNeg_formula] using h

def twistedEmbeddedGroup (m : ℕ) : EmbeddedCommutativeGroup K where
  ambientDimension := 3
  carrier := carrier K 3
  group := twistedGroup K m
  locallyClosed := locallyClosed K 3
  addition_regular := twisted_addition_regular K m
  negation_regular := twisted_negation_regular K m

def twistedEquiv (m : ℕ) : (twistedEmbeddedGroup K m).Point ≃+ (Fin 3 → K) :=
  letI := twistedGroup K m
  (untwist K m).addEquiv

def twistedProduct (m : ℕ) : EmbeddedGroupProduct K :=
  singleGroupProduct (twistedEmbeddedGroup K m)

def twistedProductEquiv (m : ℕ) : (twistedProduct K m).Point ≃+ (Fin 3 → K) where
  toFun p := twistedEquiv K m (p (0 : Fin 1))
  invFun z := fun _ => (twistedEquiv K m).symm z
  left_inv p := by
    funext i
    fin_cases i
    exact (twistedEquiv K m).symm_apply_apply _
  right_inv z := (twistedEquiv K m).apply_symm_apply z
  map_add' p q := (twistedEquiv K m).map_add (p (0 : Fin 1)) (q (0 : Fin 1))

theorem twistedProduct_embedding (m : ℕ) (p : (twistedProduct K m).Point)
    (i : (twistedProduct K m).FactorIndex) :
    (twistedProduct K m).embedding p i =
      point K 3 (shear K m 1 (twistedProductEquiv K m p)) := by
  fin_cases i
  exact congrArg Subtype.val ((twistedEquiv K m).symm_apply_apply (p (0 : Fin 1))).symm

end PhilipponMultiplicity.AffineModel

end
end

section
-- Implementation: Solutions.PhilipponProductDegree

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ProductDegree

theorem degree_fin_one (d : Fin 1 →₀ ℕ) : d.degree = d 0 := by
  simp [Finsupp.degree_eq_sum]

theorem top_fin_one (P : MvPolynomial (Fin 1) ℚ) :
    homogeneousComponent P.totalDegree P =
      monomial (Finsupp.single 0 P.totalDegree) (coeff (Finsupp.single 0 P.totalDegree) P) := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_monomial]
  have hd : d.degree = P.totalDegree ↔ Finsupp.single 0 P.totalDegree = d := by
    rw [degree_fin_one]
    constructor
    · intro h
      apply Finsupp.ext
      intro i
      fin_cases i
      simpa using h.symm
    · intro h
      rw [← h, Finsupp.single_eq_same]
  by_cases h : d.degree = P.totalDegree
  · rw [if_pos h, if_pos (hd.mp h), ← hd.mp h]
  · rw [if_neg h, if_neg (mt hd.mpr h)]

theorem degree_rename_single {ι : Type*} (i : ι) (P : MvPolynomial (Fin 1) ℚ) :
    (rename (fun _ => i) P).totalDegree = P.totalDegree := by
  have h := (weightedTotalDegree_rename_of_injective
      (w := (1 : ι → ℕ)) (P := P)
      (show Function.Injective (fun _ : Fin 1 => i) from fun _ _ _ => Subsingleton.elim _ _))
  change weightedTotalDegree 1 _ = weightedTotalDegree 1 _ at h
  simpa only [weightedTotalDegree_one] using h

end PhilipponMultiplicity.ProductDegree

namespace PhilipponMultiplicity
open SectionThree

end PhilipponMultiplicity

end
end

section
-- Implementation: Solutions.PhilipponBinomialPolynomial

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.BinomialPolynomial

def oneVariable (q a : ℕ) : MvPolynomial (Fin 1) ℚ :=
  (uniqueAlgEquiv ℚ (Fin 1)).symm (Polynomial.preHilbertPoly ℚ q a)

theorem oneVariable_coeff (q a : ℕ) (b : Fin 1 →₀ ℕ) :
    coeff b (oneVariable q a) = (Polynomial.preHilbertPoly ℚ q a).coeff (b 0) :=
  coeff_uniqueAlgEquiv_symm ℚ _ _

theorem oneVariable_degree (q a : ℕ) : (oneVariable q a).totalDegree = q := by
  classical
  apply le_antisymm
  · change (oneVariable q a).support.sup (fun b : Fin 1 →₀ ℕ => b.sum (fun _ e => e)) ≤ q
    apply Finset.sup_le
    intro b hb
    have h := mem_support_iff.mp hb
    rw [oneVariable_coeff] at h
    have ht := Polynomial.le_natDegree_of_ne_zero h
    rw [Polynomial.natDegree_preHilbertPoly] at ht
    simpa [Finsupp.sum_fintype] using ht
  · have hcoeff : coeff (Finsupp.single 0 q) (oneVariable q a) ≠ 0 := by
      rw [oneVariable_coeff, Finsupp.single_eq_same, Polynomial.coeff_preHilbertPoly_self]
      exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero q)
    simpa using le_totalDegree (mem_support_iff.mpr hcoeff)

theorem oneVariable_top (q a : ℕ) :
    homogeneousComponent q (oneVariable q a) =
      monomial (Finsupp.single 0 q) (q.factorial : ℚ)⁻¹ := by
  have h := ProductDegree.top_fin_one (oneVariable q a)
  simpa only [oneVariable_degree, oneVariable_coeff, Finsupp.single_eq_same,
    Polynomial.coeff_preHilbertPoly_self] using h

def block {ι : Type*} (i : ι) (q a : ℕ) : MvPolynomial ι ℚ :=
  rename (fun _ : Fin 1 => i) (oneVariable q a)

theorem block_degree {ι : Type*} (i : ι) (q a : ℕ) : (block i q a).totalDegree = q := by
  rw [block, ProductDegree.degree_rename_single, oneVariable_degree]

theorem block_top {ι : Type*} (i : ι) (q a : ℕ) :
    homogeneousComponent q (block i q a) =
      monomial (Finsupp.single i q) (q.factorial : ℚ)⁻¹ := by
  rw [block, ← rename_homogeneousComponent, oneVariable_top, rename_monomial]
  simp

theorem block_eval {ι : Type*} (i : ι) (q a : ℕ) (d : ι → ℕ) (ha : a ≤ d i) :
    eval (fun i => (d i : ℚ)) (block i q a) = ((d i - a + q).choose q : ℚ) := by
  rw [block, eval_rename]
  change MvPolynomial.eval₂ (RingHom.id ℚ) _
    ((uniqueAlgEquiv ℚ (Fin 1)).symm _) = _
  rw [eval₂_uniqueAlgEquiv_symm]
  exact Polynomial.preHilbertPoly_eq_choose_sub_add ℚ q ha

end PhilipponMultiplicity.BinomialPolynomial

end
end

section
-- Implementation: Solutions.PhilipponMonomialPartition

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MonomialCells

variable (p : ℕ) (N : Fin p → ℕ)

abbrev Var := Sigma fun i : Fin p => Fin (N i + 1)

theorem weight_apply (e : Var p N →₀ ℕ) (i : Fin p) :
    Finsupp.weight (Hilbert.blockWeight p N) e i = ∑ j, e ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : Fin p, ∑ j : Fin (N b + 1),
    e ⟨b,j⟩ • Hilbert.blockWeight p N ⟨b,j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

end PhilipponMultiplicity.MonomialCells

end
end

section
-- Implementation: Solutions.PhilipponProjectiveAmbientDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ProjectiveAmbientDegree
open Hilbert SectionThree

def monomialEquiv (N d : ℕ) :
    {e : MonomialCells.Var 1 (fun _ => N) →₀ ℕ //
      Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => d} ≃
    {f : Fin (N+1) → ℕ // ∑ j, f j = d} where
  toFun e := ⟨fun j => e.1 ⟨0,j⟩, by
    have h := congrFun e.2 (0 : Fin 1)
    rwa [MonomialCells.weight_apply] at h⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun v => f.1 v.2), by
    funext i
    rw [MonomialCells.weight_apply]
    simpa using f.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Finsupp.ext
    rintro ⟨i,j⟩
    fin_cases i
    rfl
  right_inv f := by
    apply Subtype.ext
    rfl

theorem degreePiece_finrank (K : Type*) [Field K] (N d : ℕ) :
    Module.finrank K (degreePiece K 1 (fun _ => N) (fun _ => d)) = (d+N).choose N := by
  classical
  unfold degreePiece
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) _).finrank_eq]
  change Module.finrank K ({e : MonomialCells.Var 1 (fun _ => N) →₀ ℕ //
    Finsupp.weight (blockWeight 1 (fun _ => N)) e = fun _ => d} →₀ K) = _
  let e := (monomialEquiv N d).trans (Sym.equivNatSumOfFintype (Fin (N+1)) d).symm
  rw [(Finsupp.domLCongr e : (_ →₀ K) ≃ₗ[K] (Sym (Fin (N+1)) d →₀ K)).finrank_eq,
    Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card,
    Sym.natCard_sym_eq_multichoose, Nat.card_fin, Nat.multichoose_eq]
  have heq : N+1+d-1 = d+N := by omega
  rw [heq, ← Nat.choose_symm (show d ≤ d+N by omega)]
  simp

theorem hilbertFunction_bot (K : Type*) [Field K] (N d : ℕ) :
    hilbertFunction K 1 (fun _ => N) ⊥ (fun _ => d) = (d+N).choose N := by
  let e := (AlgEquiv.quotientBot K (CoordinateRing K 1 (fun _ => N))).symm.toLinearEquiv
  have h := e.finrank_map_eq (degreePiece K 1 (fun _ => N) (fun _ => d))
  change Module.finrank K (quotientPiece K 1 (fun _ => N) ⊥ (fun _ => d)) = _
  exact h.trans (degreePiece_finrank K N d)

theorem hilbertPolynomial_bot (K : Type*) [Field K] (N : ℕ) :
    hilbertPolynomial K 1 (fun _ => N) ⊥ = BinomialPolynomial.block (0 : Fin 1) N 0 := by
  apply hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0,?_⟩
  intro d _
  have hd : d = fun _ => d 0 := by
    funext i
    congr 1
    exact Subsingleton.elim _ _
  rw [BinomialPolynomial.block_eval _ _ _ _ (Nat.zero_le _),hd,hilbertFunction_bot]
  simp

theorem degreeValue_bot (K : Type*) [Field K] (N d : ℕ) :
    idealDegreeValue (projectiveSpace K N) ⊥ (fun _ => d) = (d : ℚ)^N := by
  change eval (fun _ : Fin 1 => (d : ℚ))
    (((hilbertPolynomial K 1 (fun _ => N) ⊥).totalDegree.factorial : ℚ) •
      homogeneousComponent (hilbertPolynomial K 1 (fun _ => N) ⊥).totalDegree
        (hilbertPolynomial K 1 (fun _ => N) ⊥)) = _
  rw [hilbertPolynomial_bot, BinomialPolynomial.block_degree, BinomialPolynomial.block_top,
    smul_eq_C_mul,map_mul,eval_C,eval_monomial,Finsupp.prod_single_index]
  all_goals simp [Nat.factorial_ne_zero]

end PhilipponMultiplicity.ProjectiveAmbientDegree

end
end

section
-- Implementation: Solutions.PhilipponTwistedAffineDegree

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.AffineModel
universe u
variable (K : Type u) [Field K] [Infinite K]

theorem carrier_vanishingIdeal (n : ℕ) :
    (projectiveSpace K n).vanishingIdeal
      ((fun p => fun _ => p) '' carrier K n) = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  intro P hP
  change P = 0
  apply MvPolynomial.funext_set (fun _ => ({0} : Set K)ᶜ)
    (fun _ => (Set.finite_singleton (0 : K)).infinite_compl)
  intro X hX
  have hX0 : X ⟨(0 : Fin 1),(0 : Fin (n+1))⟩ ≠ 0 := hX _ (Set.mem_univ _)
  let v : Fin (n+1) → K := fun j => X ⟨(0 : Fin 1),j⟩
  have hv : v ≠ 0 := by intro h; exact hX0 (congrFun h 0)
  let p := Projectivization.mk K v hv
  have hp : p ∈ carrier K n := by
    obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
    change p.rep 0 ≠ 0
    dsimp only [p]
    rw [← hc]
    exact mul_ne_zero c.ne_zero hX0
  have hz := (projectiveSpace K n).eval_lift_eq_zero_of_mem_vanishingIdeal
    (Set.mem_image_of_mem (fun p => fun _ => p) hp) X
    (by intro i; fin_cases i; exact ⟨hv,rfl⟩) hP
  simpa only [map_zero] using hz

theorem twistedEmbeddedGroup_dimension (m : ℕ) : (twistedEmbeddedGroup K m).dimension = 3 := by
  change (Hilbert.hilbertPolynomial K 1 (fun _ => 3)
    ((projectiveSpace K 3).vanishingIdeal ((fun p => fun _ => p) '' carrier K 3))).totalDegree = 3
  rw [carrier_vanishingIdeal,ProjectiveAmbientDegree.hilbertPolynomial_bot,
    BinomialPolynomial.block_degree]

theorem twistedProduct_dimension (m : ℕ) : (twistedProduct K m).dimension = 3 := by
  change (∑ _i : Fin 1, (twistedEmbeddedGroup K m).dimension) = 3
  simp [twistedEmbeddedGroup_dimension]

theorem twistedProduct_vanishingIdeal (m : ℕ) :
    (twistedProduct K m).vanishingIdeal Set.univ = ⊥ := by
  have hi : (twistedProduct K m).embedding '' Set.univ =
      (fun p => fun _ : Fin 1 => p) '' carrier K 3 := by
    ext z
    constructor
    · rintro ⟨p,_,rfl⟩
      refine ⟨(p (0 : Fin 1)).val,(p (0 : Fin 1)).property,?_⟩
      funext i
      fin_cases i
      rfl
    · rintro ⟨p,hp,rfl⟩
      exact ⟨fun _ => ⟨p,hp⟩,Set.mem_univ _,rfl⟩
  change (projectiveSpace K 3).vanishingIdeal ((twistedProduct K m).embedding '' Set.univ) = ⊥
  rw [hi]
  exact carrier_vanishingIdeal K 3

theorem twistedProduct_degree (m d : ℕ) :
    hilbertDegreeForm (twistedProduct K m) Set.univ (fun _ => d) = (d : ℝ)^3 := by
  unfold hilbertDegreeForm
  rw [twistedProduct_vanishingIdeal]
  exact_mod_cast ProjectiveAmbientDegree.degreeValue_bot K 3 d

end PhilipponMultiplicity.AffineModel

end
end

section
-- Implementation: Solutions.PhilipponAnalyticGlobalCurve

set_option autoImplicit false
noncomputable section
open scoped Topology
namespace PhilipponMultiplicity

theorem finite_analytic_common_ball {ι : Type*} [Fintype ι]
    (f : ι → (Fin 1 → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, ∃ p : FormalMultilinearSeries ℂ (Fin 1 → ℂ) ℂ,
      HasFPowerSeriesOnBall (f i) p 0 (ENNReal.ofReal r) := by
  choose p hp using hf
  obtain ⟨r, hr⟩ := HasFPowerSeriesAt.pi hp
  obtain ⟨s, hs, hsr⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := 1) (b := r) (by simp) hr.r_pos.ne'
  have hsr' : (s : ENNReal) ≤ r := by simpa using hsr.le
  refine ⟨s, hs, fun i => ⟨p i, ?_⟩⟩
  exact (hasFPowerSeriesOnBall_pi_iff (by simpa using hs)).mp
    (hr.mono (by simpa using hs) (by simpa using hsr')) i

variable {G : EmbeddedGroupProduct ℂ}
    (curve : ℂ →+ G.Point)
    (lift : G.Point → (Fin 1 → ℂ) → G.ambient.Variable → ℂ)
    (ha : ∀ g v, AnalyticAt ℂ (fun z => lift g z v) 0)
    (hr : ∀ g t i, ∃ h : (fun j => lift g t ⟨i, j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => lift g t ⟨i, j⟩) h =
        G.embedding (g + curve (t 0)) i)

def AnalyticSubgroup.ofGlobalCurve : AnalyticSubgroup G :=
  let hb := finite_analytic_common_ball (fun v t => lift 0 t v) (ha 0)
  let r := Classical.choose hb
  let h := Classical.choose_spec hb
  { parameterDimension := 1
    parameterDimension_pos := by decide
    radius := r
    radius_pos := h.1
    domain := Metric.ball 0 r
    domain_eq_ball := rfl
    domain_open := Metric.isOpen_ball
    zero_mem := Metric.mem_ball_self h.1
    map := fun t => curve (t.val 0)
    map_zero := curve.map_zero
    map_add := fun x y _ => curve.map_add (x.val 0) (y.val 0)
    lift := lift
    lift_analytic := ha
    base_series := h.2
    base_represents := fun t i => by simpa using hr 0 t.val i
    lift_represents := fun g => by
      filter_upwards [Metric.ball_mem_nhds (0 : Fin 1 → ℂ) h.1] with t ht
      exact ⟨ht, hr g t⟩ }

end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions.PhilipponTwistedContactModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.TwistedContact
open AffineModel

abbrev G (m : ℕ) := twistedProduct ℂ m
abbrev coordinates (m : ℕ) := twistedProductEquiv ℂ m

def curve (m : ℕ) : ℂ →+ (G m).Point :=
  (coordinates m).symm.toAddMonoidHom.comp
    { toFun := fun t => ![0,t,0]
      map_zero' := by ext i; fin_cases i <;> rfl
      map_add' := by intros; ext i; fin_cases i <;> simp }

@[simp] theorem curve_coordinates (m : ℕ) (t : ℂ) :
    coordinates m (curve m t) = ![0,t,0] := (coordinates m).apply_symm_apply _

def lift (m : ℕ) (g : (G m).Point) (t : Fin 1 → ℂ)
    (v : (G m).ambient.Variable) : ℂ :=
  ![1,coordinates m g 0,coordinates m g 1+t 0,
    coordinates m g 2+(coordinates m g 0)^m*(coordinates m g 1+t 0)] v.2

theorem lift_analytic (m : ℕ) (g : (G m).Point) (v : (G m).ambient.Variable) :
    AnalyticAt ℂ (fun t => lift m g t v) 0 := by
  have ht : AnalyticAt ℂ (fun t : Fin 1 → ℂ => t 0) 0 :=
    (ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt 0
  rcases v with ⟨i,j⟩
  fin_cases i
  fin_cases j
  · exact analyticAt_const
  · exact analyticAt_const
  · exact analyticAt_const.add ht
  · exact analyticAt_const.add (analyticAt_const.mul (analyticAt_const.add ht))

theorem lift_represents (m : ℕ) (g : (G m).Point) (t : Fin 1 → ℂ)
    (i : (G m).FactorIndex) :
    ∃ h : (fun j => lift m g t ⟨i,j⟩) ≠ 0,
      Projectivization.mk ℂ (fun j => lift m g t ⟨i,j⟩) h =
        (G m).embedding (g+curve m (t 0)) i := by
  have he : coordinates m (g+curve m (t 0)) =
      ![coordinates m g 0,coordinates m g 1+t 0,coordinates m g 2] := by
    ext j
    fin_cases j <;> simp
  have hv : (fun j => lift m g t ⟨i,j⟩) ≠ 0 := by
    intro h
    have hh := congrFun h (0 : Fin 4)
    simpa [lift] using hh
  refine ⟨hv,?_⟩
  rw [twistedProduct_embedding,he]
  unfold point
  congr 1
  funext j
  fin_cases j <;> simp [lift,shear]

def analytic (m : ℕ) : AnalyticSubgroup (G m) :=
  AnalyticSubgroup.ofGlobalCurve (curve m) (lift m) (lift_analytic m) (lift_represents m)

def axisPoint (m : ℕ) (u : ℂ) : (G m).Point := (coordinates m).symm ![u,0,0]

@[simp] theorem axisPoint_coordinates (m : ℕ) (u : ℂ) :
    coordinates m (axisPoint m u) = ![u,0,0] := (coordinates m).apply_symm_apply _

theorem axis_pullback (m : ℕ) (u : ℂ) (P : (G m).CoordinateRing)
    (t : Fin 1 → ℂ) :
    (analytic m).pullback P (axisPoint m u) t =
      MvPolynomial.eval (fun v : (G m).ambient.Variable =>
        (![1,u,t 0,u^m*t 0] : Fin 4 → ℂ) v.2) P := by
  change MvPolynomial.eval (lift m (axisPoint m u) t) P = _
  apply congrArg (fun f => MvPolynomial.eval f P)
  funext v
  simp [lift]

end PhilipponMultiplicity.TwistedContact

end
end

section
-- Implementation: Solutions.PhilipponTwistedContactCandidate

set_option autoImplicit false

namespace PhilipponMultiplicity.ContactEmbeddingReview

theorem exponent_map_injective
    (i j k i' j' k' : ℕ)
    (hi : i ≤ 400) (hi' : i' ≤ 400)
    (hx : i + 401 * k = i' + 401 * k')
    (ht : j + k = j' + k') :
    i = i' ∧ j = j' ∧ k = k' := by
  omega

theorem numerical_budget :
    (Nat.choose (400 + 1) 1 : ℝ) * 1 * 400 ≤
      (1 / ((4 : ℝ)^3 * (Nat.factorial 3 : ℝ))) * 400^3 := by
  norm_num

end PhilipponMultiplicity.ContactEmbeddingReview

end

section
-- Implementation: Solutions.PhilipponTwistedSurface

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.TwistedContact

def surfaceExponent (d : (G 401).ambient.Variable →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![d ⟨(0 : Fin 1),1⟩ + 401*d ⟨(0 : Fin 1),3⟩,
      d ⟨(0 : Fin 1),2⟩ + d ⟨(0 : Fin 1),3⟩]

def surfacePolynomial (P : (G 401).CoordinateRing) : MvPolynomial (Fin 2) ℂ :=
  ∑ d ∈ P.support, MvPolynomial.monomial (surfaceExponent d) (P.coeff d)

theorem surface_eval (P : (G 401).CoordinateRing) (u t : ℂ) :
    MvPolynomial.eval ![u,t] (surfacePolynomial P) =
      MvPolynomial.eval (fun v : (G 401).ambient.Variable =>
        (![1,u,t,u^401*t] : Fin 4 → ℂ) v.2) P := by
  classical
  rw [surfacePolynomial,map_sum,MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro d hd
  rw [MvPolynomial.eval_monomial]
  change P.coeff d * (surfaceExponent d).prod (fun i n => (![u,t] i)^n) =
    P.coeff d * d.prod (fun i n => (![1,u,t,u^401*t] : Fin 4 → ℂ) i.2 ^ n)
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  change P.coeff d * (∏ i : Fin 2, (![u,t] i)^(surfaceExponent d i)) =
    P.coeff d * (∏ v : (i : Fin 1) × Fin 4, (![1,u,t,u^401*t] v.2)^d v)
  rw [Fintype.prod_sigma]
  change P.coeff d * (∏ i : Fin 2, (![u,t] i)^(surfaceExponent d i)) =
    P.coeff d * (∏ i : Fin 1, ∏ j : Fin 4, (![1,u,t,u^401*t] j)^d ⟨i,j⟩)
  simp [surfaceExponent,Fin.prod_univ_one,Fin.prod_univ_two,Fin.prod_univ_four,pow_add,mul_pow,pow_mul]
  ring_nf
  simp

theorem surfaceExponent_injective_on_support
    (P : (G 401).CoordinateRing)
    (hP : (G 401).ambient.IsHomogeneous P (fun _ => 400)) :
    Set.InjOn surfaceExponent (P.support : Set _) := by
  intro d hd e he hde
  have hd' := hP d hd (0 : Fin 1)
  have he' := hP e he (0 : Fin 1)
  change (∑ j : Fin 4, d ⟨(0 : Fin 1),j⟩) = 400 at hd'
  change (∑ j : Fin 4, e ⟨(0 : Fin 1),j⟩) = 400 at he'
  simp only [Fin.sum_univ_four] at hd' he'
  have hx := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hde
  have ht := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hde
  simp [surfaceExponent] at hx ht
  obtain ⟨h1,h2,h3⟩ := ContactEmbeddingReview.exponent_map_injective
    (d ⟨(0 : Fin 1),1⟩) (d ⟨(0 : Fin 1),2⟩) (d ⟨(0 : Fin 1),3⟩)
    (e ⟨(0 : Fin 1),1⟩) (e ⟨(0 : Fin 1),2⟩) (e ⟨(0 : Fin 1),3⟩)
    (by omega) (by omega) hx ht
  have h0 : d ⟨(0 : Fin 1),0⟩ = e ⟨(0 : Fin 1),0⟩ := by omega
  ext v
  rcases v with ⟨i,j⟩
  fin_cases i
  change Fin 4 at j
  fin_cases j <;> assumption

theorem eq_zero_of_surfacePolynomial_eq_zero
    (P : (G 401).CoordinateRing)
    (hP : (G 401).ambient.IsHomogeneous P (fun _ => 400))
    (hz : surfacePolynomial P = 0) : P = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_zero]
  by_cases hd : d ∈ P.support
  · have hc := congrArg (MvPolynomial.coeff (surfaceExponent d)) hz
    rw [surfacePolynomial,MvPolynomial.coeff_sum] at hc
    have he : (∑ e ∈ P.support,
        (MvPolynomial.monomial (surfaceExponent e) (P.coeff e)).coeff (surfaceExponent d)) =
        P.coeff d := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro e he hed
        have hne : surfaceExponent e ≠ surfaceExponent d :=
          fun h => hed (surfaceExponent_injective_on_support P hP he hd h)
        simp [MvPolynomial.coeff_monomial,hne]
      · exact fun hn => (hn hd).elim
    rw [he,MvPolynomial.coeff_zero] at hc
    exact hc
  · exact MvPolynomial.notMem_support_iff.mp hd

theorem eq_zero_of_surface_eval_zero
    (P : (G 401).CoordinateRing)
    (hP : (G 401).ambient.IsHomogeneous P (fun _ => 400))
    (hz : ∀ u t : ℂ, MvPolynomial.eval
      (fun v : (G 401).ambient.Variable => (![1,u,t,u^401*t] : Fin 4 → ℂ) v.2) P = 0) :
    P = 0 := by
  apply eq_zero_of_surfacePolynomial_eq_zero P hP
  apply MvPolynomial.funext
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx,surface_eval]
  exact (hz _ _).trans (map_zero _).symm

end PhilipponMultiplicity.TwistedContact

end
end

section
-- Implementation: Solutions.PhilipponPointHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity

end PhilipponMultiplicity
end
end

section
-- Implementation: Solutions.PhilipponParametrizedHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem hilbertFunction_eq_finrank_image
    {T A : Type*} [CommRing A] [Algebra K A]
    (p : T → M.Point) (φ : M.CoordinateRing →ₐ[K] A) (D : M.FactorIndex → ℕ)
    (hker : ∀ P : M.CoordinateRing, M.IsHomogeneous P D →
      (φ P = 0 ↔ ∀ t, M.eval P (p t) = 0)) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        φ.toLinearMap) := by
  let V := Hilbert.degreePiece K M.factorCount M.ambientDimension D
  let I := M.vanishingIdeal (Set.range p)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict V
  let g := φ.toLinearMap.domRestrict V
  have hfg : LinearMap.ker f = LinearMap.ker g := by
    ext P
    change Ideal.Quotient.mk I P.val = 0 ↔ φ P.val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hker P.val ((M.degreePiece_iff _ _).mp P.property)]
    constructor
    · intro h t
      exact M.eval_eq_zero_of_mem_vanishingIdeal h (Set.mem_range_self t)
    · intro h
      exact Ideal.subset_span ⟨⟨D, (M.degreePiece_iff _ _).mp P.property⟩,
        by rintro x ⟨t, rfl⟩; exact h t⟩
  have hf : LinearMap.range f = V.map (Ideal.Quotient.mkₐ K I).toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have hg : LinearMap.range g = V.map φ.toLinearMap := by
    ext x
    constructor
    · rintro ⟨P, rfl⟩
      exact ⟨P.val, P.property, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨⟨P, hP⟩, rfl⟩
  have he := (f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hfg).trans g.quotKerEquivRange)).finrank_eq
  rw [hf, hg] at he
  exact he

theorem hilbertFunction_eq_finrank_polynomial_image [Infinite K]
    (p : K → M.Point) (v : M.Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (D : M.FactorIndex → ℕ) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D =
      Module.finrank K ((Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        (MvPolynomial.aeval v).toLinearMap) := by
  apply M.hilbertFunction_eq_finrank_image p (MvPolynomial.aeval v) D
  intro P hP
  have hev (t : K) : (MvPolynomial.aeval v P : Polynomial K).eval t =
      MvPolynomial.eval (fun j => (v j).eval t) P := by
    clear hP
    induction P using MvPolynomial.induction_on with
    | C c => simp
    | add P Q hP hQ => simp [hP, hQ]
    | mul_X P j hP => simp [hP]
  constructor
  · intro hz t
    apply (M.eval_eq_zero_iff_of_lift (p t) (fun j => (v j).eval t) (hrep t) P D hP).mp
    rw [← hev, hz, Polynomial.eval_zero]
  · intro hz
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_zero, hev]
    exact (M.eval_eq_zero_iff_of_lift (p t) (fun j => (v j).eval t) (hrep t) P D hP).mpr (hz t)

theorem polynomial_image_natDegree_le
    (v : M.Variable → Polynomial K) (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (P : M.CoordinateRing) (hP : M.IsHomogeneous P D) :
    (MvPolynomial.aeval v P : Polynomial K).natDegree ≤ ∑ i, D i * δ i := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  change ((Polynomial.C (MvPolynomial.coeff d P)) * _).natDegree ≤ _
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C, zero_add]
  change (d.prod (fun j n => v j ^ n)).natDegree ≤ _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ j : M.Variable, (v j ^ d j).natDegree ≤ ∑ j : M.Variable, d j * δ j.1 := by
      apply Finset.sum_le_sum
      intro j _
      exact (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hv j))
    _ = ∑ i, D i * δ i := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      change (∑ y, d ⟨i, y⟩ * δ i) = _
      rw [← Finset.sum_mul, hP d hd i]

theorem polynomial_image_eq_degreeLT
    (v : M.Variable → Polynomial K) (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (hlift : ∀ k ≤ ∑ i, D i * δ i, ∃ P : M.CoordinateRing,
      M.IsHomogeneous P D ∧ MvPolynomial.aeval v P = Polynomial.X ^ k) :
    (Hilbert.degreePiece K M.factorCount M.ambientDimension D).map
        (MvPolynomial.aeval v).toLinearMap =
      Polynomial.degreeLT K ((∑ i, D i * δ i) + 1) := by
  classical
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    rw [Polynomial.degreeLT_succ_eq_degreeLE, Polynomial.mem_degreeLE]
    exact Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr
      (M.polynomial_image_natDegree_le v δ D hv P ((M.degreePiece_iff _ _).mp hP)))
  · rw [Polynomial.degreeLT_eq_span_X_pow, Submodule.span_le]
    intro Q hQ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨P, hP, heq⟩ := hlift k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    exact ⟨P, (M.degreePiece_iff _ _).mpr hP, heq⟩

theorem hilbertFunction_polynomial_parametrization [Infinite K]
    (p : K → M.Point) (v : M.Variable → Polynomial K)
    (hrep : ∀ t i, ∃ h : (fun j => (v ⟨i, j⟩).eval t) ≠ 0,
      Projectivization.mk K (fun j => (v ⟨i, j⟩).eval t) h = p t i)
    (δ D : M.FactorIndex → ℕ)
    (hv : ∀ j, (v j).natDegree ≤ δ j.1)
    (hlift : ∀ k ≤ ∑ i, D i * δ i, ∃ P : M.CoordinateRing,
      M.IsHomogeneous P D ∧ MvPolynomial.aeval v P = Polynomial.X ^ k) :
    Hilbert.hilbertFunction K M.factorCount M.ambientDimension
      (M.vanishingIdeal (Set.range p)) D = (∑ i, D i * δ i) + 1 := by
  rw [M.hilbertFunction_eq_finrank_polynomial_image p v hrep D,
    M.polynomial_image_eq_degreeLT v δ D hv hlift,
    (Polynomial.degreeLTEquiv K _).finrank_eq]
  simp

end PhilipponMultiplicity.MultiProjectiveSpace

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] {p : ℕ} {N : Fin p → ℕ}

theorem degreeForm_of_hilbertPolynomial_linear
    (I : Ideal (CoordinateRing K p N)) (R : MvPolynomial (Fin p) ℚ)
    (hR : R.IsHomogeneous 1) (hne : R ≠ 0)
    (hP : hilbertPolynomial K p N I = R + 1) :
    degreeForm K p N I = R := by
  have hd : (R + 1).totalDegree = 1 := by
    rw [MvPolynomial.totalDegree_add_eq_left_of_totalDegree_lt]
    · exact hR.totalDegree hne
    · simp [hR.totalDegree hne]
  simp only [degreeForm, hP, hd, Nat.factorial_one, Nat.cast_one, one_smul, map_add]
  rw [MvPolynomial.homogeneousComponent_eq_self hR,
    MvPolynomial.homogeneousComponent_eq_zero 1 1 (by simp : (1 : MvPolynomial (Fin p) ℚ).totalDegree < 1), add_zero]

end PhilipponMultiplicity.Hilbert
end
end

section
-- Implementation: Solutions.PhilipponTwistedAxis

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.TwistedContact
open AffineModel

def axisGroup (m : ℕ) : AddSubgroup (G m).Point where
  carrier := {g | coordinates m g 1 = 0 ∧ coordinates m g 2 = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simpa [ha.1,ha.2,hb.1,hb.2]
  neg_mem' := by intro a ha; simpa [ha.1,ha.2]

theorem mem_axisGroup (m : ℕ) (g : (G m).Point) :
    g ∈ axisGroup m ↔ ∃ u, axisPoint m u = g := by
  constructor
  · intro hg
    refine ⟨coordinates m g 0,(coordinates m).injective ?_⟩
    ext j
    fin_cases j <;> simp [hg.1,hg.2]
  · rintro ⟨u,rfl⟩
    change _ = 0 ∧ _ = 0
    simp

theorem axisPoint_embedding (m : ℕ) (u : ℂ) (i : (G m).FactorIndex) :
    (G m).embedding (axisPoint m u) i = point ℂ 3 ![u,0,0] := by
  rw [twistedProduct_embedding,axisPoint_coordinates]
  congr 1
  ext j
  fin_cases j <;> simp [shear]

def coordinatePolynomial (m : ℕ) (j : Fin 4) : (G m).CoordinateRing :=
  MvPolynomial.X ⟨(0 : Fin 1),j⟩

theorem coordinatePolynomial_homogeneous (m : ℕ) (j : Fin 4) :
    (G m).ambient.IsHomogeneous (coordinatePolynomial m j) (fun _ => 1) := by
  convert (G m).ambient.isHomogeneous_X ⟨(0 : Fin 1),j⟩ using 1
  · rfl
  · funext i
    fin_cases i
    rfl

theorem coordinatePolynomial_zero (m : ℕ) (j : Fin 4) (g : (G m).Point) :
    (G m).ambient.eval (coordinatePolynomial m j) ((G m).embedding g) = 0 ↔
      lift m g 0 ⟨(0 : Fin 1),j⟩ = 0 := by
  have hr (i : (G m).FactorIndex) := lift_represents m g 0 i
  simp only [Pi.zero_apply,map_zero,add_zero] at hr
  simpa [coordinatePolynomial] using
    ((G m).ambient.eval_eq_zero_iff_of_lift ((G m).embedding g) (lift m g 0)
      hr (coordinatePolynomial m j) (fun _ => 1)
      (coordinatePolynomial_homogeneous m j)).symm

theorem axisGroup_closed (m : ℕ) :
    @IsClosed _ (G m).zariskiTopology (axisGroup m : Set (G m).Point) := by
  letI := (G m).ambient.zariskiTopology
  letI := (G m).zariskiTopology
  have he : (axisGroup m : Set (G m).Point) =
      {g | (G m).ambient.eval (coordinatePolynomial m 2) ((G m).embedding g) = 0} ∩
      {g | (G m).ambient.eval (coordinatePolynomial m 3) ((G m).embedding g) = 0} := by
    ext g
    simp only [Set.mem_inter_iff,Set.mem_setOf_eq,coordinatePolynomial_zero]
    change (_ = 0 ∧ _ = 0) ↔ _
    simp [lift]
    intro h1
    simp [h1]
  rw [he]
  exact ((G m).ambient.isClosed_zero _ _ (coordinatePolynomial_homogeneous m 2)).preimage
      continuous_induced_dom |>.inter
    (((G m).ambient.isClosed_zero _ _ (coordinatePolynomial_homogeneous m 3)).preimage
      continuous_induced_dom)

def axis (m : ℕ) : AlgebraicSubgroup (G m) := ⟨axisGroup m,axisGroup_closed m⟩

theorem axis_carrier (m : ℕ) : (axis m).carrier = Set.range (axisPoint m) := by
  ext g
  exact mem_axisGroup m g

def axisPolynomialLift (m : ℕ) (v : (G m).ambient.Variable) : Polynomial ℂ :=
  ![1,Polynomial.X,0,0] v.2

theorem axisPolynomialLift_represents (m : ℕ) (u : ℂ) (i : (G m).FactorIndex) :
    ∃ h : (fun j => (axisPolynomialLift m ⟨i,j⟩).eval u) ≠ 0,
      Projectivization.mk ℂ (fun j => (axisPolynomialLift m ⟨i,j⟩).eval u) h =
        (G m).embedding (axisPoint m u) i := by
  have he : (fun j => (axisPolynomialLift m ⟨i,j⟩).eval u) =
      (Fin.cons 1 ![u,0,0] : Fin 4 → ℂ) := by
    change (fun j : Fin 4 => (axisPolynomialLift m ⟨i,j⟩).eval u) = _
    ext j
    fin_cases j <;> simp [axisPolynomialLift]
  have hn : (fun j => (axisPolynomialLift m ⟨i,j⟩).eval u) ≠ 0 := by
    rw [he]
    intro h
    have := congrFun h 0
    simpa using this
  refine ⟨hn,?_⟩
  rw [axisPoint_embedding]
  unfold point
  congr 1

theorem axis_hilbertFunction (m : ℕ) (D : (G m).FactorIndex → ℕ) :
    Hilbert.hilbertFunction ℂ 1 (fun _ => 3) ((G m).vanishingIdeal (axis m).carrier) D =
      D (0 : Fin 1) + 1 := by
  classical
  have he : (G m).embedding '' (axis m).carrier =
      Set.range (fun u => (G m).embedding (axisPoint m u)) := by
    rw [axis_carrier,← Set.range_comp']
  change Hilbert.hilbertFunction _ _ _ ((G m).ambient.vanishingIdeal _) _ = _
  rw [he]
  have h := (G m).ambient.hilbertFunction_polynomial_parametrization
    (fun u => (G m).embedding (axisPoint m u)) (axisPolynomialLift m)
    (axisPolynomialLift_represents m) (fun _ => 1) D ?_ ?_
  · change _ = (∑ i : Fin 1, D i * 1) + 1 at h
    simpa using h
  · intro v
    rcases v with ⟨i,j⟩
    fin_cases i
    change Fin 4 at j
    fin_cases j <;> simp [axisPolynomialLift]
  · intro k hk
    change k ≤ ∑ i : Fin 1, D i * 1 at hk
    have hk' : k ≤ D (0 : Fin 1) := by simpa using hk
    refine ⟨coordinatePolynomial m 1 ^ k * coordinatePolynomial m 0 ^ (D (0 : Fin 1)-k),?_,?_⟩
    · convert ((coordinatePolynomial_homogeneous m 1).pow _ k).mul _
        ((coordinatePolynomial_homogeneous m 0).pow _ (D (0 : Fin 1)-k)) using 1
      ext i
      fin_cases i
      simp
      omega
    · simp [coordinatePolynomial,axisPolynomialLift]

theorem axis_hilbertPolynomial (m : ℕ) :
    Hilbert.hilbertPolynomial ℂ 1 (fun _ => 3) ((G m).vanishingIdeal (axis m).carrier) =
      MvPolynomial.X (0 : Fin 1) + 1 := by
  apply Hilbert.hilbertPolynomial_eq_of_isHilbertPolynomial
  refine ⟨0,?_⟩
  intro D _
  rw [axis_hilbertFunction]
  simp

theorem axis_degree (m d : ℕ) :
    hilbertDegreeForm (G m) (axis m).carrier (fun _ => d) = d := by
  have hf := Hilbert.degreeForm_of_hilbertPolynomial_linear
    ((G m).vanishingIdeal (axis m).carrier) (MvPolynomial.X (0 : Fin 1))
    (MvPolynomial.isHomogeneous_X ℚ _) (MvPolynomial.X_ne_zero _) (axis_hilbertPolynomial m)
  unfold hilbertDegreeForm Hilbert.degreeValue
  change ((MvPolynomial.eval (fun _ : Fin 1 => (d : ℚ))
    (Hilbert.degreeForm ℂ 1 (fun _ => 3) ((G m).vanishingIdeal (axis m).carrier))) : ℝ) = d
  change Hilbert.degreeForm ℂ 1 (fun _ => 3) _ = _ at hf
  rw [hf]
  simp

end PhilipponMultiplicity.TwistedContact

end
end

section
-- Implementation: Solutions.PhilipponTwistedAxisCodimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.TwistedContact

theorem axis_coordinate_mem_ideal (m : ℕ) :
    coordinatePolynomial m 2 ∈ (G m).vanishingIdeal (axis m).carrier := by
  apply Ideal.subset_span
  refine ⟨⟨fun _ => 1,coordinatePolynomial_homogeneous m 2⟩,?_⟩
  rintro p ⟨g,hg,rfl⟩
  apply (coordinatePolynomial_zero m 2 g).mpr
  obtain ⟨u,rfl⟩ := (mem_axisGroup m g).mp hg
  simp [lift]

theorem axis_tangentKernel (m : ℕ) :
    (analytic m).tangentKernel (axis m).carrier = ⊥ := by
  let ev : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.piUnique ℂ (fun _ : Fin 1 => ℂ)
  have hf : (analytic m).pullback (coordinatePolynomial m 2) 0 = ev := by
    funext t
    change MvPolynomial.eval (lift m 0 t) (coordinatePolynomial m 2) = _
    simp [coordinatePolynomial,lift,ev]
  apply le_antisymm ?_ bot_le
  intro t ht
  change t = 0
  change t ∈ ⨅ Q : {Q : (G m).CoordinateRing // Q ∈ (G m).vanishingIdeal (axis m).carrier},
    LinearMap.ker (fderiv ℂ ((analytic m).pullback Q.val 0) 0).toLinearMap at ht
  have hp := ((Submodule.mem_iInf _).mp ht) ⟨_,axis_coordinate_mem_ideal m⟩
  change (fderiv ℂ ((analytic m).pullback (coordinatePolynomial m 2) 0) 0) t = 0 at hp
  rw [hf,ev.hasFDerivAt.fderiv] at hp
  exact ev.injective (hp.trans ev.map_zero.symm)

theorem axis_analyticCodimension (m : ℕ) :
    analyticCodimension (analytic m) (axis m).carrier = 1 := by
  unfold analyticCodimension
  rw [axis_tangentKernel]
  simp
  rfl

end PhilipponMultiplicity.TwistedContact

end
end

section
-- Implementation: Solutions.PhilipponPolynomialJetRigidity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity.PolynomialJetRigidity

theorem iteratedDeriv_eval (p : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun t => p.eval t) z = (Polynomial.derivative^[n] p).eval z := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun t => p.eval t) = fun t => p.derivative.eval t :=
      funext fun t => p.deriv
    rw [hd,ih,Function.iterate_succ_apply]

theorem eq_zero_of_jet (p : Polynomial ℂ) (N : ℕ) (hd : p.natDegree ≤ N)
    (hj : ∀ n ≤ N, iteratedFDeriv ℂ n (fun t : Fin 1 → ℂ => p.eval (t 0)) 0 = 0) :
    p = 0 := by
  have hs (n : ℕ) (hn : n ≤ N) : iteratedDeriv n (fun t => p.eval t) 0 = 0 := by
    let ev : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
    have hc : ContDiff ℂ (n : ℕ) (fun t => p.eval t) := by
      clear hd hj
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simpa using hp.add hq
      | monomial k c =>
        simpa using (contDiff_const.mul (contDiff_id.pow k) :
          ContDiff ℂ (n : ℕ) (fun t : ℂ => c*t^k))
    have he := ev.iteratedFDeriv_comp_right hc 0 le_rfl
    have hv := congrArg (fun L : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => Fin 1 → ℂ) ℂ => L (fun _ _ => 1)) he
    change iteratedFDeriv ℂ n (fun t : Fin 1 → ℂ => p.eval (t 0)) 0 _ = _ at hv
    rw [hj n hn] at hv
    simpa [iteratedDeriv,ev,ContinuousMultilinearMap.compContinuousLinearMap_apply] using hv.symm
  ext n
  simp only [Polynomial.coeff_zero]
  by_cases hn : n ≤ N
  · have h := hs n hn
    rw [iteratedDeriv_eval,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_iterate_derivative] at h
    simpa [Nat.descFactorial_self,nsmul_eq_mul,Nat.factorial_ne_zero] using h
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (Nat.lt_of_not_ge hn))

end PhilipponMultiplicity.PolynomialJetRigidity

end
end

section
-- Implementation: Solutions.PhilipponTwistedContactRigidity

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.TwistedContact

def timeLift (u : ℂ) (v : (G 401).ambient.Variable) : Polynomial ℂ :=
  ![1,Polynomial.C u,Polynomial.X,Polynomial.C (u^401)*Polynomial.X] v.2

def timePolynomial (P : (G 401).CoordinateRing) (u : ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval (timeLift u) P

theorem timePolynomial_eval (P : (G 401).CoordinateRing) (u t : ℂ) :
    (timePolynomial P u).eval t =
      MvPolynomial.eval (fun v : (G 401).ambient.Variable =>
        (![1,u,t,u^401*t] : Fin 4 → ℂ) v.2) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [timePolynomial]
  | add P Q hP hQ => simpa [timePolynomial] using congrArg₂ (· + ·) hP hQ
  | mul_X P v hP =>
    simp only [timePolynomial,map_mul,MvPolynomial.aeval_X,Polynomial.eval_mul,
      MvPolynomial.eval_X] at *
    rw [hP]
    congr 1
    rcases v with ⟨i,j⟩
    change Fin 4 at j
    fin_cases j <;> simp [timeLift]

theorem timePolynomial_degree (P : (G 401).CoordinateRing)
    (hP : (G 401).ambient.IsHomogeneous P (fun _ => 400)) (u : ℂ) :
    (timePolynomial P u).natDegree ≤ 400 := by
  have h := (G 401).ambient.polynomial_image_natDegree_le (timeLift u)
    (fun _ => 1) (fun _ => 400) ?_ P hP
  · change (timePolynomial P u).natDegree ≤ ∑ _i : Fin 1, 400*1 at h
    simpa using h
  · intro v
    rcases v with ⟨i,j⟩
    change Fin 4 at j
    fin_cases j <;> simp [timeLift]
    have hm := Polynomial.natDegree_C_mul_le (u^401) (Polynomial.X : Polynomial ℂ)
    rw [map_pow,Polynomial.natDegree_X] at hm
    exact hm

theorem degree400_contact_forces_zero (P : (G 401).CoordinateRing)
    (hP : (G 401).ambient.IsHomogeneous P (fun _ => 400))
    (hcontact : ∀ h ∈ (axis 401).carrier,
      (401 : WithTop ℕ) ≤ vanishingOrder (analytic 401) P h) : P = 0 := by
  apply eq_zero_of_surface_eval_zero P hP
  intro u t
  have hz : timePolynomial P u = 0 := by
    apply PolynomialJetRigidity.eq_zero_of_jet _ 400 (timePolynomial_degree P hP u)
    intro n hn
    have hc := hcontact (axisPoint 401 u) (by rw [axis_carrier]; exact Set.mem_range_self u)
    have hj := (natCast_le_jetOrder_iff (n := 401)
      (f := (analytic 401).pullback P (axisPoint 401 u)) (x := 0)).mp hc n (by omega)
    have hf : (analytic 401).pullback P (axisPoint 401 u) =
        (fun s : Fin 1 → ℂ => (timePolynomial P u).eval (s 0)) := by
      ext s
      rw [axis_pullback,timePolynomial_eval]
    rwa [hf] at hj
  rw [← timePolynomial_eval,hz,Polynomial.eval_zero]

end PhilipponMultiplicity.TwistedContact

end
end

section
-- Implementation: Solutions.PhilipponTwistedContactObstruction

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity.TwistedContact
open AffineModel

theorem complex_base : IsPhilipponBaseField ℂ :=
  Or.inl ⟨RingEquiv.refl ℂ,isometry_id⟩

theorem numerical_hypothesis :
    (Nat.choose (400 + analyticCodimension (analytic 401) (axis 401).carrier)
      (analyticCodimension (analytic 401) (axis 401).carrier) : ℝ) *
      (cosetCount ({0} : Finset (G 401).Point) (axis 401).carrier : ℝ) *
      hilbertDegreeForm (G 401) (axis 401).carrier (fun _ => 400) ≤
    (1 / ((4 : ℝ) ^ (G 401).dimension * ((G 401).dimension.factorial : ℝ))) *
      hilbertDegreeForm (G 401) Set.univ (fun _ => 400) := by
  rw [axis_analyticCodimension,axis_degree,twistedProduct_dimension,twistedProduct_degree]
  simpa [cosetCount] using ContactEmbeddingReview.numerical_budget

theorem bottom_contact_iff (P : (G 401).CoordinateRing)
    (hP : IsMultihomogeneousOfDegree (G 401) P (fun _ => 400)) :
    (P ∈ (⊥ : Ideal (G 401).CoordinateRing) ↔
      ∀ g ∈ ({0} : Finset (G 401).Point), ∀ h ∈ (axis 401).carrier,
        ((400 + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder (analytic 401) P (g+h)) := by
  classical
  constructor
  · intro hP
    have hp : P = 0 := hP
    subst P
    intro g hg h hh
    have hf : (analytic 401).pullback 0 (g+h) = fun _ => 0 := by
      ext t
      exact map_zero _
    apply (natCast_le_jetOrder_iff (n := 401)).mpr
    intro k hk
    rw [hf]
    simp
  · intro hc
    change P = 0
    apply degree400_contact_forces_zero P hP
    intro h hh
    simpa using hc 0 (Finset.mem_singleton_self _) h hh

theorem no_contact_gap : ¬ (∀
    (K : Type) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D)
    (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))),
    Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D <
      Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D) := by
  classical
  intro claim
  have h := claim ℂ complex_base (G 401)
    (by rw [twistedProduct_dimension]; decide) (analytic 401)
    {0} (Finset.mem_singleton_self _) 400 (fun _ => 400)
    (by intro i; rw [twistedProduct_degree]; norm_num)
    (axis 401) numerical_hypothesis ⊥ bottom_contact_iff
  rw [twistedProduct_vanishingIdeal] at h
  exact (lt_irrefl _ h)

end PhilipponMultiplicity.TwistedContact

end
end

open PhilipponMultiplicity
open scoped BigOperators Topology

theorem solution : ¬ (∀
    (K : Type) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension) (A : AnalyticSubgroup G)
    (sample : Finset G.Point) (hsample : 0 ∈ sample) (T : ℕ) (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ))
    (H : AlgebraicSubgroup G)
    (hbound :
      (Nat.choose (T + analyticCodimension A H.carrier) (analyticCodimension A H.carrier) : ℝ) *
          (cosetCount sample H.carrier : ℝ) * hilbertDegreeForm G H.carrier D ≤
        (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
          hilbertDegreeForm G Set.univ D)
    (J : Ideal G.CoordinateRing)
    (hJ : ∀ P : G.CoordinateRing, IsMultihomogeneousOfDegree G P D →
      (P ∈ J ↔ ∀ g ∈ sample, ∀ h ∈ H.carrier,
        ((T + 1 : ℕ) : WithTop ℕ) ≤ vanishingOrder A P (g + h))),
    Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension J D <
      Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D) := by
  exact TwistedContact.no_contact_gap
