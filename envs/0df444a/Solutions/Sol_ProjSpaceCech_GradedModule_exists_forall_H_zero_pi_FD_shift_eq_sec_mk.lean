-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8d707fa3-5aca-5069-a60d-1b23278be861

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk

set_option autoImplicit false

universe u

noncomputable section

namespace H0FreeBody

open ProjSpaceCech ProjSpaceCech.GradedModule MvPolynomial

variable {R : Type u} [CommRing R] {n : ℕ}

def toF (v : Fin (n + 1) → ℕ) : Fin (n + 1) →₀ ℕ := ∑ j, Finsupp.single j (v j)

@[scoped simp] theorem toF_apply (v : Fin (n + 1) → ℕ) (i : Fin (n + 1)) : toF v i = v i := by
  simp [toF, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem toF_add (v w : Fin (n + 1) → ℕ) : toF (v + w) = toF v + toF w := by
  ext i; simp [Pi.add_apply]

theorem toF_zero : toF (0 : Fin (n + 1) → ℕ) = 0 := by ext i; simp

theorem prod_X_pow_eq (v : Fin (n + 1) → ℕ) :
    (∏ j, (X j : MvPolynomial (Fin (n + 1)) R) ^ v j) = monomial (toF v) 1 := by
  rw [toF, monomial_sum_one]
  exact Finset.prod_congr rfl (fun j _ => X_pow_eq_monomial)

theorem pi_monMul_apply {ι : Type} [Fintype ι] (Dk : ι → GradedModule R n) (v : Fin (n + 1) → ℕ)
    (m : (GradedModule.pi Dk).M) (k : ι) :
    GradedModule.monMul (GradedModule.pi Dk) v m k = GradedModule.monMul (Dk k) v (m k) := by
  unfold GradedModule.monMul
  suffices h : ∀ (s : Finset (Fin (n + 1))) (hc : _) (hc' : _),
      (s.noncommProd (fun j => (GradedModule.pi Dk).xMul j ^ v j) hc) m k =
        (s.noncommProd (fun j => (Dk k).xMul j ^ v j) hc') (m k) from h Finset.univ _ _
  have hpow : ∀ (j : Fin (n + 1)) (a : ℕ) (q : (GradedModule.pi Dk).M),
      (((GradedModule.pi Dk).xMul j ^ a) q) k = ((Dk k).xMul j ^ a) (q k) := by
    intro j a q
    induction a generalizing q with
    | zero => rfl
    | succ a ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl
  intro s
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | insert j s hj ih =>
    intro hc hc'
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj, Finset.noncommProd_insert_of_notMem _ _ _ _ hj,
      Module.End.mul_apply, Module.End.mul_apply, hpow,
      ih (hc.mono (by simp [Finset.subset_insert])) (hc'.mono (by simp [Finset.subset_insert]))]

theorem shift_monMul (D : GradedModule R n) (d₀ : ℤ) (v : Fin (n + 1) → ℕ) (m : D.M) :
    GradedModule.monMul (GradedModule.shift D d₀) v m = GradedModule.monMul D v m := rfl

variable {ι : Type} [Fintype ι] (e : ι → ℤ) (d : ℤ)

abbrev Fsh : GradedModule R n :=
  GradedModule.shift (GradedModule.pi fun k => GradedModule.FD R n (e k)) d

theorem monMul_Fsh_apply (v : Fin (n + 1) → ℕ) (p : (Fsh (R := R) (n := n) e d).M) (k : ι) :
    GradedModule.monMul (Fsh e d) v p k = monomial (toF v) 1 * (show MvPolynomial (Fin (n + 1)) R from p k) := by
  show GradedModule.monMul (GradedModule.pi fun k => GradedModule.FD R n (e k)) v p k = _
  rw [pi_monMul_apply]
  show GradedModule.monMul (GradedModule.free R n) v (p k) = _
  rw [free_monMul_apply, prod_X_pow_eq]
  rfl

theorem monMul_Fsh_injective (v : Fin (n + 1) → ℕ) : Function.Injective (GradedModule.monMul (Fsh (R := R) (n := n) e d) v) := by
  intro p q h
  funext k
  have := congrFun h k
  change GradedModule.monMul (GradedModule.pi fun k => GradedModule.FD R n (e k)) v p k =
    GradedModule.monMul (GradedModule.pi fun k => GradedModule.FD R n (e k)) v q k at this
  rw [pi_monMul_apply, pi_monMul_apply] at this
  exact free_monMul_injective v this

theorem coeff_monomial_one_mul (u m : Fin (n + 1) →₀ ℕ) (q : MvPolynomial (Fin (n + 1)) R) :
    coeff m (monomial u 1 * q) = if u ≤ m then coeff (m - u) q else 0 := by
  rw [coeff_monomial_mul']; simp

theorem le_add_of_monomial_mul_eq {u u' : Fin (n + 1) →₀ ℕ} {q q' : MvPolynomial (Fin (n + 1)) R}
    (h : monomial u 1 * q = monomial u' 1 * q') {m : Fin (n + 1) →₀ ℕ} (hm : m ∈ q.support) : u' ≤ u + m := by
  have h1 : coeff (u + m) (monomial u 1 * q) = coeff m q := by
    rw [coeff_monomial_one_mul, if_pos le_self_add, add_tsub_cancel_left]
  have h2 := congrArg (coeff (u + m)) h
  rw [h1, coeff_monomial_one_mul] at h2
  by_contra hle
  rw [if_neg hle] at h2
  exact (mem_support_iff.1 hm) h2

def divM (q : MvPolynomial (Fin (n + 1)) R) (u : Fin (n + 1) →₀ ℕ) : MvPolynomial (Fin (n + 1)) R :=
  ∑ m ∈ q.support, monomial (m - u) (coeff m q)

theorem monomial_mul_divM {q : MvPolynomial (Fin (n + 1)) R} {u : Fin (n + 1) →₀ ℕ}
    (h : ∀ m ∈ q.support, u ≤ m) : monomial u 1 * divM q u = q := by
  rw [divM, Finset.mul_sum]
  conv_rhs => rw [as_sum q]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [monomial_mul, one_mul, add_tsub_cancel_of_le (h m hm)]

theorem divM_isHomogeneous {q : MvPolynomial (Fin (n + 1)) R} {u : Fin (n + 1) →₀ ℕ} {N : ℕ}
    (hq : q.IsHomogeneous N) (h : ∀ m ∈ q.support, u ≤ m) : (divM q u).IsHomogeneous (N - u.degree) := by
  rw [divM]
  refine IsHomogeneous.sum _ _ _ fun m hm => isHomogeneous_monomial _ ?_
  have hmN : m.degree = N := by
    have := hq (mem_support_iff.1 hm)
    simp [Finsupp.weight_apply, Finsupp.degree_apply] at this
    exact this
  have : (m - u) + u = m := tsub_add_cancel_of_le (h m hm)
  have hdeg := congrArg Finsupp.degree this
  rw [map_add] at hdeg
  omega

theorem sec_mk_num_congr (D : GradedModule R n) (I : Finset (Fin (n + 1))) (a : Fin (n + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0)
    {m m' : D.M} (hmm : m = m') (hm : m ∈ D.grade (∑ j, (a j : ℤ))) (hm' : m' ∈ D.grade (∑ j, (a j : ℤ))) :
    GradedModule.sec.mk D I ⟨a, ha, m, hm⟩ = GradedModule.sec.mk D I ⟨a, ha, m', hm'⟩ := by
  subst hmm; rfl

theorem mem_img_zero_iff (s : Idx n 0) (j : Fin (n + 1)) : j ∈ Idx.img n s ↔ j = s.1 0 := by
  simp only [Idx.img, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩; rw [Fin.fin_one_eq_zero a]
  · rintro rfl; exact ⟨0, rfl⟩

theorem Idx_zero_ext {s s' : Idx n 0} (h : s.1 0 = s'.1 0) : s = s' :=
  Subtype.ext (funext fun a => by rw [Fin.fin_one_eq_zero a]; exact h)

def pairIdx (i j : Fin (n + 1)) (hij : i < j) : Idx n 1 :=
  ⟨![i, j], fun a b hab => by
    fin_cases a <;> fin_cases b <;> simp_all⟩

theorem face_pairIdx_zero (i j : Fin (n + 1)) (hij : i < j) : (Idx.face n (pairIdx i j hij) 0).1 0 = j := by
  simp [Idx.face, pairIdx, Fin.succAbove_zero]

theorem face_pairIdx_one (i j : Fin (n + 1)) (hij : i < j) : (Idx.face n (pairIdx i j hij) 1).1 0 = i := by
  simp [Idx.face, pairIdx]

end H0FreeBody
p2m_reactivate "P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody"

end
p2m_reactivate "P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk.H0FreeBody"

open H0FreeBody ProjSpaceCech ProjSpaceCech.GradedModule MvPolynomial in
theorem solution
    (R : Type u) [CommRing R] (n : ℕ) {ι : Type} [Fintype ι] (e : ι → ℤ) :
    ∃ d₁ : ℤ, ∀ d : ℤ, d₁ ≤ d →
      ∀ c : ProjSpaceCech.GradedModule.H
          (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d) 0,
        ∃ f : (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)).M,
          f ∈ (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)).grade d ∧
          ∃ hf : f ∈ (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d).grade
              (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
            ∀ s : ProjSpaceCech.Idx n 0,
              (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d
                  (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d) 0))
                from c).1 s =
                ProjSpaceCech.GradedModule.sec.mk
                  (ProjSpaceCech.GradedModule.shift (ProjSpaceCech.GradedModule.pi fun k => ProjSpaceCech.GradedModule.FD R n (e k)) d)
                  (ProjSpaceCech.Idx.img n s) ⟨0, fun _ _ => rfl, f, hf⟩ := by
  classical
  refine ⟨∑ k, ((e k).natAbs : ℤ), fun d hd c => ?_⟩
  have hde : ∀ k, 0 ≤ d + e k := fun k => by
    have h1 : ((e k).natAbs : ℤ) ≤ ∑ k, ((e k).natAbs : ℤ) :=
      Finset.single_le_sum (f := fun k => ((e k).natAbs : ℤ)) (fun _ _ => by positivity) (Finset.mem_univ k)
    have h2 : -(e k) ≤ ((-(e k)).natAbs : ℤ) := Int.le_natAbs
    rw [Int.natAbs_neg] at h2
    omega

  let x : ∀ s : Idx n 0, GradedModule.Frac (H0FreeBody.Fsh (R := R) (n := n) e d) (Idx.img n s) := fun s => Quotient.out ((show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (H0FreeBody.Fsh (R := R) (n := n) e d) 0)) from c).1 s)
  have hx : ∀ s, (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (H0FreeBody.Fsh (R := R) (n := n) e d) 0)) from c).1 s = GradedModule.sec.mk (H0FreeBody.Fsh (R := R) (n := n) e d) (Idx.img n s) (x s) := fun s => (Quotient.out_eq _).symm
  have hsupp : ∀ (s : Idx n 0) (j : Fin (n + 1)), j ≠ s.1 0 → (x s).denExp j = 0 :=
    fun s j hj => (x s).hden j (by rw [mem_img_zero_iff]; exact hj)
  have htoF : ∀ s : Idx n 0, toF (x s).denExp = Finsupp.single (s.1 0) ((x s).denExp (s.1 0)) := fun s => by
    ext j
    rw [toF_apply, Finsupp.single_apply]
    by_cases h : s.1 0 = j
    · subst h; simp
    · rw [if_neg h, hsupp s j (Ne.symm h)]

  have hnum : ∀ (s : Idx n 0) (k : ι), 0 ≤ (∑ j, ((x s).denExp j : ℤ)) + d + e k ∧
      ((x s).num k).IsHomogeneous ((∑ j, ((x s).denExp j : ℤ)) + d + e k).toNat := by
    intro s k
    have hnn : 0 ≤ (∑ j, ((x s).denExp j : ℤ)) + d + e k := by
      have : 0 ≤ ∑ j, ((x s).denExp j : ℤ) := Finset.sum_nonneg fun _ _ => by positivity
      have := hde k; omega
    have h := (x s).hnum k (Set.mem_univ k)
    change (x s).num k ∈ GradedModule.freeGrade R n ((∑ j, ((x s).denExp j : ℤ)) + d + e k) at h
    rw [GradedModule.freeGrade_of_nonneg R n hnn] at h
    exact ⟨hnn, (mem_homogeneousSubmodule _ _).1 h⟩

  have hrel_of_lt : ∀ (s s' : Idx n 0) (hlt : s.1 0 < s'.1 0), ∃ cc : Fin (n + 1) → ℕ,
      GradedModule.monMul (H0FreeBody.Fsh (R := R) (n := n) e d) (cc + (x s).denExp) (x s').num =
        GradedModule.monMul (H0FreeBody.Fsh (R := R) (n := n) e d) (cc + (x s').denExp) (x s).num := by
    intro s s' hlt
    let t : Idx n 1 := pairIdx (s.1 0) (s'.1 0) hlt
    have hs' : Idx.face n t 0 = s' := Idx_zero_ext (face_pairIdx_zero _ _ hlt)
    have hs : Idx.face n t 1 = s := Idx_zero_ext (face_pairIdx_one _ _ hlt)
    have h0 := congrFun (show GradedModule.d (H0FreeBody.Fsh (R := R) (n := n) e d) 0 (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (H0FreeBody.Fsh (R := R) (n := n) e d) 0)) from c).1 = 0 from (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (H0FreeBody.Fsh (R := R) (n := n) e d) 0)) from c).2) t
    rw [GradedModule.d_apply, Fin.sum_univ_two] at h0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Pi.zero_apply] at h0
    rw [add_neg_eq_zero, hx, hx, GradedModule.faceRes, GradedModule.faceRes, GradedModule.secIncl_mk,
      GradedModule.secIncl_mk] at h0
    obtain ⟨cc, -, hrel⟩ := (GradedModule.sec_mk_eq _ _).1 h0
    dsimp only at hrel
    rw [hs, hs'] at hrel
    exact ⟨cc, hrel⟩

  have hdiv : ∀ (s : Idx n 0) (k : ι), ∀ m ∈ ((x s).num k).support, toF (x s).denExp ≤ m := by
    intro s k m hm
    rw [htoF, Finsupp.single_le_iff]
    by_cases hex : ∃ j : Fin (n + 1), j ≠ s.1 0
    · obtain ⟨j, hj⟩ := hex
      let sj : Idx n 0 := ⟨fun _ => j, fun a b hab => absurd hab (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)⟩
      have hsj : sj.1 0 = j := rfl
      have hz : (x sj).denExp (s.1 0) = 0 := hsupp sj (s.1 0) (by rw [hsj]; exact hj.symm)
      have key : ∀ cc : Fin (n + 1) → ℕ,
          GradedModule.monMul (H0FreeBody.Fsh (R := R) (n := n) e d) (cc + (x sj).denExp) (x s).num =
            GradedModule.monMul (H0FreeBody.Fsh (R := R) (n := n) e d) (cc + (x s).denExp) (x sj).num →
          (x s).denExp (s.1 0) ≤ m (s.1 0) := by
        intro cc hcc
        have hk := congrFun hcc k
        rw [monMul_Fsh_apply, monMul_Fsh_apply] at hk
        have hle := le_add_of_monomial_mul_eq hk hm (s.1 0)
        simp only [Finsupp.add_apply, toF_apply, Pi.add_apply, hz] at hle
        omega
      rcases lt_or_gt_of_ne hj with hlt | hgt
      ·
        obtain ⟨cc, hcc⟩ := hrel_of_lt sj s (by rw [hsj]; exact hlt)
        exact key cc hcc
      · obtain ⟨cc, hcc⟩ := hrel_of_lt s sj (by rw [hsj]; exact hgt)
        exact key cc hcc.symm
    ·
      push Not at hex
      obtain ⟨hnn, hhom⟩ := hnum s k
      have hdeg : m.degree = ((∑ j, ((x s).denExp j : ℤ)) + d + e k).toNat := by
        have := hhom (mem_support_iff.1 hm)
        simp [Finsupp.weight_apply, Finsupp.degree_apply] at this
        exact this
      have huniv : (Finset.univ : Finset (Fin (n + 1))) = {s.1 0} :=
        Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_univ _, fun j _ => hex j⟩
      have hdm : m.degree = m (s.1 0) := by
        rw [Finsupp.degree_apply]
        rw [Finset.sum_subset (m.support.subset_univ.trans huniv.le) (fun j _ hj => Finsupp.notMem_support_iff.1 hj)]
        exact Finset.sum_singleton _ _
      have hsum : (∑ j, ((x s).denExp j : ℤ)) = (x s).denExp (s.1 0) := by
        rw [huniv, Finset.sum_singleton]
      have := Int.toNat_of_nonneg hnn
      rw [hsum] at this hdeg
      have hde' := hde k
      omega

  let fd : ∀ s : Idx n 0, (H0FreeBody.Fsh (R := R) (n := n) e d).M := fun s k => divM ((x s).num k) (toF (x s).denExp)
  have hP : ∀ s, (x s).num = GradedModule.monMul (H0FreeBody.Fsh (R := R) (n := n) e d) (x s).denExp (fd s) := fun s => funext fun k => by
    rw [monMul_Fsh_apply]; exact (monomial_mul_divM (hdiv s k)).symm
  have hdeg_toF : ∀ s : Idx n 0, (toF (x s).denExp).degree = ∑ j, (x s).denExp j := fun s => by
    rw [toF, map_sum]; exact Finset.sum_congr rfl fun j _ => Finsupp.degree_single _ _
  have hfd_hom : ∀ (s : Idx n 0) (k : ι), (fd s k).IsHomogeneous (d + e k).toNat := fun s k => by
    obtain ⟨hnn, hhom⟩ := hnum s k
    have h := divM_isHomogeneous hhom (hdiv s k)
    rw [hdeg_toF] at h
    have hde' := hde k
    have : ((∑ j, ((x s).denExp j : ℤ)) + d + e k).toNat - ∑ j, (x s).denExp j = (d + e k).toNat := by
      have h1 := Int.toNat_of_nonneg hnn
      have h2 := Int.toNat_of_nonneg hde'
      have h3 : ((∑ j, (x s).denExp j : ℕ) : ℤ) = ∑ j, ((x s).denExp j : ℤ) := by push_cast; rfl
      omega
    rw [this] at h
    exact h
  have hfd_mem : ∀ s : Idx n 0, fd s ∈ (H0FreeBody.Fsh (R := R) (n := n) e d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)) :=
    fun s k _ => by
      show fd s k ∈ GradedModule.freeGrade R n ((∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)) + d + e k)
      simp only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero, zero_add]
      rw [GradedModule.freeGrade_of_nonneg R n (hde k)]
      exact (mem_homogeneousSubmodule _ _).2 (hfd_hom s k)
  have hfd_mem' : ∀ s : Idx n 0, fd s ∈ (GradedModule.pi fun k => GradedModule.FD R n (e k)).grade d :=
    fun s k _ => by
      show fd s k ∈ GradedModule.freeGrade R n (d + e k)
      rw [GradedModule.freeGrade_of_nonneg R n (hde k)]
      exact (mem_homogeneousSubmodule _ _).2 (hfd_hom s k)
  have hcs : ∀ s : Idx n 0, (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (H0FreeBody.Fsh (R := R) (n := n) e d) 0)) from c).1 s = GradedModule.sec.mk (H0FreeBody.Fsh (R := R) (n := n) e d) (Idx.img n s) ⟨0, fun _ _ => rfl, fd s, hfd_mem s⟩ := by
    intro s
    rw [hx s]
    refine (GradedModule.sec_mk_eq _ _).2 ⟨0, fun _ _ => rfl, ?_⟩
    show GradedModule.monMul (H0FreeBody.Fsh (R := R) (n := n) e d) (0 + 0) (x s).num = GradedModule.monMul (H0FreeBody.Fsh (R := R) (n := n) e d) (0 + (x s).denExp) (fd s)
    rw [hP s, ← GradedModule.monMul_add_apply]
    exact GradedModule.monMul_congr _ (fun j => by simp) _

  have hind : ∀ s s' : Idx n 0, fd s = fd s' := by
    have aux : ∀ (s s' : Idx n 0), s.1 0 < s'.1 0 → fd s = fd s' := by
      intro s s' hlt
      obtain ⟨cc, hcc⟩ := hrel_of_lt s s' hlt
      rw [hP s, hP s', ← GradedModule.monMul_add_apply, ← GradedModule.monMul_add_apply] at hcc
      rw [GradedModule.monMul_congr _ (show ∀ j, (cc + (x s).denExp + (x s').denExp) j = (cc + (x s').denExp + (x s).denExp) j
        from fun j => by simp only [Pi.add_apply]; ring)] at hcc
      exact (monMul_Fsh_injective e d _ hcc).symm
    intro s s'
    rcases lt_trichotomy (s.1 0) (s'.1 0) with h | h | h
    · exact aux s s' h
    · rw [Idx_zero_ext h]
    · exact (aux s' s h).symm

  let s₀ : Idx n 0 := ⟨fun _ => 0, fun a b hab => absurd hab (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)⟩
  refine ⟨fd s₀, hfd_mem' s₀, hfd_mem s₀, fun s => ?_⟩
  rw [hcs s]
  exact sec_mk_num_congr _ _ _ _ (hind s s₀) _ _

end S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk (solution)
