-- Prove2me | solution 1 for QSVT19.Main.theorem_17
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-15T04:47:55.670294+00:00
-- url     : https://prove2.me/submissions/9beb3907-2156-475b-b1c5-c6bab19a1626

import Definitions.Def_QSVT19_Main_Setting
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open Matrix QSVT19.Main
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTBlock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev ip (v w : ι → ℂ) : ℂ := star v ⬝ᵥ w
lemma frame_fixed {d : ℕ} (v : Fin d → ι → ℂ)
    (ho : ∀ i j, ip (v i) (v j) = if i=j then 1 else 0) (i : Fin d) :
    (∑ j, vecMulVec (v j) (star (v j))) *ᵥ v i = v i := by
  simp only [Matrix.sum_mulVec,vecMulVec_mulVec]
  simp only [op_smul_eq_smul,ho]
  simp
lemma P_fixed {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (i : Fin S.d) : P*ᵥS.ψ i=S.ψ i := by
  exact (congrArg (fun M : Matrix ι ι ℂ => M*ᵥS.ψ i) S.span_ψ).trans (frame_fixed S.ψ S.orthonormal_ψ i)
lemma Q_fixed {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (i : Fin S.dt) : Q*ᵥS.ψt i=S.ψt i := by
  exact (congrArg (fun M : Matrix ι ι ℂ => M*ᵥS.ψt i) S.span_ψt).trans (frame_fixed S.ψt S.orthonormal_ψt i)
lemma ip_adjoint (M : Matrix ι ι ℂ) (v w : ι → ℂ) : ip v (M*ᵥw) = ip (Mᴴ*ᵥv) w := by
  simp only [ip,star_mulVec,conjTranspose_conjTranspose,dotProduct_mulVec,vecMul_vecMul]
lemma unitary_left (U : Matrix ι ι ℂ) (hU : U ∈ unitaryGroup ι ℂ) : Uᴴ*U=1 := by
  exact Matrix.mem_unitaryGroup_iff'.mp hU
lemma unitary_right (U : Matrix ι ι ℂ) (hU : U ∈ unitaryGroup ι ℂ) : U*Uᴴ=1 := by
  exact Matrix.mem_unitaryGroup_iff.mp hU
lemma svd_action {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) :
    Q*ᵥ(U*ᵥS.ψ j) = ∑ i : Fin (min S.d S.dt),
      if Fin.castLE (min_le_left S.d S.dt) i = j then (S.ς i:ℂ) • S.ψtmin i else 0 := by
  have hh := congrArg (fun M : Matrix ι ι ℂ => M*ᵥS.ψ j) S.svd
  simp only [← mulVec_mulVec,P_fixed,Matrix.sum_mulVec,Matrix.smul_mulVec,vecMulVec_mulVec] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  simp only [op_smul_eq_smul]
  change (S.ς i:ℂ) • (ip (S.ψ _) (S.ψ j) • S.ψtmin i) = _
  simp only [ip,S.orthonormal_ψ]
  split_ifs <;> simp_all
lemma svd_adjoint_action {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (j : Fin S.dt) :
    P*ᵥ(Uᴴ*ᵥS.ψt j) = ∑ i : Fin (min S.d S.dt),
      if Fin.castLE (min_le_right S.d S.dt) i = j then (S.ς i:ℂ) • S.ψmin i else 0 := by
  have hh := congrArg (fun M : Matrix ι ι ℂ => Mᴴ*ᵥS.ψt j) S.svd
  have hp : Pᴴ=P := hP.isSelfAdjoint
  have hq : Qᴴ=Q := hQ.isSelfAdjoint
  simp only [conjTranspose_mul,conjTranspose_sum,conjTranspose_smul,conjTranspose_vecMulVec,
    star_star,Complex.star_def,Complex.conj_ofReal,hp,hq,← mulVec_mulVec,Q_fixed,
    Matrix.sum_mulVec,Matrix.smul_mulVec,vecMulVec_mulVec] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i _
  simp only [op_smul_eq_smul]
  change (S.ς i:ℂ) • (ip (S.ψt _) (S.ψt j) • S.ψmin i) = _
  simp only [ip,S.orthonormal_ψt]
  split_ifs <;> simp_all
end QSVTBlock

noncomputable section
open Matrix QSVT19.Main
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTBlock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma delta_sum {m d : ℕ} (h : m ≤ d) (f : Fin m → ι → ℂ) (j : Fin d) :
    (∑ i : Fin m, if Fin.castLE h i = j then f i else 0) =
      if hj : j.val < m then f ⟨j.val,hj⟩ else 0 := by
  classical
  by_cases hj : j.val < m
  · rw [dif_pos hj]
    rw [Finset.sum_eq_single (⟨j.val,hj⟩:Fin m)]
    · simp [Fin.ext_iff]
    · intro b _ hb
      have hn : Fin.castLE h b ≠ j := by intro hh;apply hb;apply Fin.ext;exact congrArg (fun z : Fin d => z.val) hh
      simp [hn]
    · simp
  · rw [dif_neg hj]
    apply Finset.sum_eq_zero
    intro i _
    have hn : Fin.castLE h i ≠ j := by intro hh;have := congrArg Fin.val hh; simp only [Fin.val_castLE] at this;omega
    simp [hn]
def leftVec {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) : ι → ℂ :=
  if hj : j.val < min S.d S.dt then S.ψtmin ⟨j.val,hj⟩ else 0
lemma ext_nonneg {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) : 0 ≤ S.ςext j := by
  unfold ProjUnitarySVD.ςext
  split_ifs <;> first | exact S.ς_nonneg _ | exact le_rfl
lemma ext_forward {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) :
    Q*ᵥ(U*ᵥS.ψ j) = (S.ςext j:ℂ) • leftVec S j := by
  rw [svd_action,delta_sum]
  unfold ProjUnitarySVD.ςext leftVec
  split_ifs <;> simp
lemma ext_backward {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (j : Fin S.d) :
    P*ᵥ(Uᴴ*ᵥleftVec S j) = (S.ςext j:ℂ) • S.ψ j := by
  unfold leftVec ProjUnitarySVD.ςext
  split_ifs with hj
  · unfold ProjUnitarySVD.ψtmin
    rw [svd_adjoint_action S hP hQ,delta_sum]
    simp only [Fin.val_castLE,dif_pos hj]
    rfl
  · simp
lemma left_fixed {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) : Q*ᵥleftVec S j=leftVec S j := by
  unfold leftVec
  split_ifs <;> first | exact Q_fixed S _ | simp
lemma ip_smul_right (v w : ι → ℂ) (a : ℂ) : ip v (a • w)=a*ip v w := by
  simp [ip,dotProduct,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]
lemma ip_smul_left (v w : ι → ℂ) (a : ℂ) : ip (a • v) w=conj a*ip v w := by
  simp [ip,dotProduct,Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]
lemma ip_sub_left (u v w : ι → ℂ) : ip (u-v) w=ip u w-ip v w := by simp [ip,sub_dotProduct]
lemma ip_sub_right (u v w : ι → ℂ) : ip u (v-w)=ip u v-ip u w := by simp [ip,dotProduct_sub]
lemma ip_sym (v w : ι → ℂ) : ip v w=conj (ip w v) := by
  simp [ip,dotProduct, mul_comm]
lemma ip_unitary (U : Matrix ι ι ℂ) (hU : U ∈ unitaryGroup ι ℂ) (v w : ι → ℂ) : ip (U*ᵥv) (U*ᵥw)=ip v w := by
  rw [ip_adjoint, mulVec_mulVec,unitary_left U hU,one_mulVec]
lemma ip_nonneg (v : ι → ℂ) : 0 ≤ (ip v v).re := by
  have hh := inner_self_nonneg (𝕜:=ℂ) (x:=WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm] at hh
  exact hh
lemma ip_zero (v : ι → ℂ) (h : ip v v=0) : v=0 := by
  have hh : inner ℂ (WithLp.toLp 2 v) (WithLp.toLp 2 v)=0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm];exact h
  have hh' := (inner_self_eq_zero (𝕜:=ℂ)).mp hh
  exact congrArg WithLp.ofLp hh'
end QSVTBlock

noncomputable section
open Matrix QSVT19.Main
open scoped ComplexConjugate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTBlock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma left_norm {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) :
    ip (leftVec S j) (leftVec S j) = if j.val < min S.d S.dt then 1 else 0 := by
  unfold leftVec
  split_ifs
  · simpa only [ip,ProjUnitarySVD.ψtmin,ite_true] using S.orthonormal_ψt (Fin.castLE (min_le_right S.d S.dt) ⟨j.val,by assumption⟩) (Fin.castLE (min_le_right S.d S.dt) ⟨j.val,by assumption⟩)
  · simp [ip]
lemma cross {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (hQ : IsStarProjection Q) (j : Fin S.d) :
    ip (leftVec S j) (U*ᵥS.ψ j) = (S.ςext j:ℂ) := by
  have hq : Qᴴ=Q := hQ.isSelfAdjoint
  have hh := ip_adjoint Q (leftVec S j) (U*ᵥS.ψ j)
  rw [hq,left_fixed] at hh
  rw [← hh,ext_forward,ip_smul_right,left_norm]
  unfold ProjUnitarySVD.ςext
  split_ifs <;> simp
lemma residual_ip {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hU : U ∈ unitaryGroup ι ℂ) (hQ : IsStarProjection Q) (j : Fin S.d) :
    ip (U*ᵥS.ψ j-(S.ςext j:ℂ) • leftVec S j) (U*ᵥS.ψ j-(S.ςext j:ℂ) • leftVec S j) =
      1-(S.ςext j:ℂ)^2 := by
  have hv : ip (S.ψ j) (S.ψ j)=1 := by simpa [ip] using S.orthonormal_ψ j j
  have hc : ip (U*ᵥS.ψ j) (leftVec S j)=(S.ςext j:ℂ) := by
    rw [ip_sym,cross S hQ,Complex.conj_ofReal]
  simp only [ip_sub_left,ip_sub_right,ip_smul_left,ip_smul_right,ip_unitary U hU,hv,
    hc,cross S hQ,Complex.conj_ofReal,left_norm]
  unfold ProjUnitarySVD.ςext
  split_ifs <;> simp <;> ring
lemma ext_le_one {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hU : U ∈ unitaryGroup ι ℂ) (hQ : IsStarProjection Q) (j : Fin S.d) : S.ςext j ≤ 1 := by
  have hh := ip_nonneg (U*ᵥS.ψ j-(S.ςext j:ℂ) • leftVec S j)
  rw [residual_ip S hU hQ] at hh
  rw [pow_two] at hh
  simp only [Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hh
  nlinarith [ext_nonneg S j]
lemma residual_one {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hU : U ∈ unitaryGroup ι ℂ) (hQ : IsStarProjection Q) (j : Fin S.d) (hx : S.ςext j=1) :
    U*ᵥS.ψ j=leftVec S j := by
  have hh := residual_ip S hU hQ j
  rw [hx] at hh
  simp only [Complex.ofReal_one,one_smul,one_pow,sub_self] at hh
  exact sub_eq_zero.mp (ip_zero _ hh)
end QSVTBlock

noncomputable section
open Matrix QSVT19.Main QAlgorithms
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTBlock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def pair (v w : ι → ℂ) : Matrix ι (Fin 2) ℂ := fun i j => if j=0 then v i else w i
lemma mul_pair (M : Matrix ι ι ℂ) (v w : ι → ℂ) : M*pair v w=pair (M*ᵥv) (M*ᵥw) := by
  ext i j;fin_cases j <;>simp [pair,mul_apply,mulVec,dotProduct]
lemma pair_R (v w : ι → ℂ) (x : ℝ) :
    pair v w*reflR x = pair ((x:ℂ) • v+(Real.sqrt (1-x^2):ℂ) • w)
      ((Real.sqrt (1-x^2):ℂ) • v-(x:ℂ) • w) := by
  ext i j;fin_cases j <;>simp [pair,reflR,mul_apply,Fin.sum_univ_two] <;> ring
lemma R_square (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) : reflR x*reflR x=1 := by
  have hh : 0 ≤ 1-x^2 := by nlinarith [hx.1,hx.2]
  have hs : (Real.sqrt (1-x^2):ℂ)^2=1-(x:ℂ)^2 := by exact_mod_cast Real.sq_sqrt hh
  ext i j;fin_cases i <;>fin_cases j <;>simp [reflR,mul_apply,Fin.sum_univ_two]
  all_goals first | linear_combination hs | ring
lemma phase_vec (M : Matrix ι ι ℂ) (v w : ι → ℂ) (hv : M*ᵥv=v) (hw : M*ᵥw=0) (a : ℝ) :
    phaseRefl a M*pair v w=pair v w*qspZ a := by
  have h0 : phaseRefl a M*ᵥv=Complex.exp (a*Complex.I) • v := by
    simp [phaseRefl,add_mulVec,smul_mulVec,sub_mulVec,hv]
  have h1 : phaseRefl a M*ᵥw=Complex.exp (-(a*Complex.I)) • w := by
    simp [phaseRefl,add_mulVec,smul_mulVec,sub_mulVec,hw]
  rw [mul_pair,h0,h1]
  ext i j;fin_cases j <;>simp [pair,qspZ,mul_apply,Fin.sum_univ_two] <;>ring
lemma pair_first (v w : ι → ℂ) : (pair v w).col 0=v := rfl
lemma projected_pair (M : Matrix ι ι ℂ) (v w : ι → ℂ) (hv : M*ᵥv=v) (hw : M*ᵥw=0)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    M*ᵥ((pair v w*A).col 0) = A 0 0 • v := by
  have hh : (pair v w*A).col 0 = A 0 0 • v + A 1 0 • w := by
    funext i
    simp [Matrix.col,Matrix.mul_apply,Fin.sum_univ_two,pair]
    ring
  rw [hh,mulVec_add,mulVec_smul,mulVec_smul,hv,hw,smul_zero,add_zero]
end QSVTBlock

noncomputable section
open Matrix QSVT19.Main
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTBlock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def rightRest {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) : ι → ℂ :=
  (Real.sqrt (1-S.ςext j^2):ℂ)⁻¹ • (Uᴴ*ᵥleftVec S j-(S.ςext j:ℂ) • S.ψ j)
def leftRest {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) : ι → ℂ :=
  (Real.sqrt (1-S.ςext j^2):ℂ)⁻¹ • (U*ᵥS.ψ j-(S.ςext j:ℂ) • leftVec S j)
lemma rightRest_null {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (j : Fin S.d) : P*ᵥrightRest S j=0 := by
  simp only [rightRest,mulVec_smul,mulVec_sub,ext_backward S hP hQ,P_fixed,sub_self,smul_zero]
lemma leftRest_null {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q) (j : Fin S.d) : Q*ᵥleftRest S j=0 := by
  simp only [leftRest,mulVec_smul,mulVec_sub,ext_forward,left_fixed,sub_self,smul_zero]
lemma U_vectors {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hU : U ∈ unitaryGroup ι ℂ) (hQ : IsStarProjection Q) (j : Fin S.d) :
    U*ᵥS.ψ j = (S.ςext j:ℂ) • leftVec S j+(Real.sqrt (1-S.ςext j^2):ℂ) • leftRest S j ∧
    U*ᵥrightRest S j = (Real.sqrt (1-S.ςext j^2):ℂ) • leftVec S j-(S.ςext j:ℂ) • leftRest S j := by
  let x := S.ςext j
  let c : ℂ := (Real.sqrt (1-x^2):ℂ)
  have hx0 : 0 ≤ x := ext_nonneg S j
  have hx1 : x ≤ 1 := ext_le_one S hU hQ j
  have hs : c^2=1-(x:ℂ)^2 := by
    dsimp [c]
    exact_mod_cast Real.sq_sqrt (show 0 ≤ 1-x^2 by nlinarith)
  by_cases h1 : x=1
  · have hc : c=0 := by simp [c,h1]
    have hv := residual_one S hU hQ j h1
    simp only [rightRest,leftRest]
    change U*ᵥS.ψ j = (x:ℂ) • leftVec S j+c • (c⁻¹ • _) ∧
      U*ᵥ(c⁻¹ • _) = c • leftVec S j-(x:ℂ) • (c⁻¹ • _)
    simp [hc,h1,hv]
  · have hc : c ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      have hxl : x < 1 := lt_of_le_of_ne hx1 h1
      nlinarith [mul_pos (sub_pos.mpr hxl) (show 0 < 1+x by linarith)]
    constructor
    · change _ = (x:ℂ) • _+c • (c⁻¹ • _)
      rw [smul_smul,mul_inv_cancel₀ hc,one_smul,add_sub_cancel]
    · change U*ᵥ(c⁻¹ • (Uᴴ*ᵥleftVec S j-(x:ℂ) • S.ψ j)) =
        c • leftVec S j-(x:ℂ) • (c⁻¹ • (U*ᵥS.ψ j-(x:ℂ) • leftVec S j))
      rw [mulVec_smul,mulVec_sub,mulVec_smul,mulVec_mulVec,unitary_right U hU,one_mulVec]
      funext k
      simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
      field_simp
      linear_combination -(leftVec S j k)*hs
lemma blocks {U P Q : Matrix ι ι ℂ} (S : ProjUnitarySVD U P Q)
    (hU : U ∈ unitaryGroup ι ℂ) (hQ : IsStarProjection Q) (j : Fin S.d) :
    U*pair (S.ψ j) (rightRest S j) = pair (leftVec S j) (leftRest S j)*reflR (S.ςext j) ∧
    Uᴴ*pair (leftVec S j) (leftRest S j) = pair (S.ψ j) (rightRest S j)*reflR (S.ςext j) := by
  have h := U_vectors S hU hQ j
  have hh : U*pair (S.ψ j) (rightRest S j) = pair (leftVec S j) (leftRest S j)*reflR (S.ςext j) := by
    rw [mul_pair,pair_R,h.1,h.2]
  refine ⟨hh,?_⟩
  have hr := R_square (S.ςext j) ⟨by linarith [ext_nonneg S j],ext_le_one S hU hQ j⟩
  have hl : pair (leftVec S j) (leftRest S j) = U*pair (S.ψ j) (rightRest S j)*reflR (S.ςext j) := by
    rw [hh,Matrix.mul_assoc,hr,Matrix.mul_one]
  rw [hl,← Matrix.mul_assoc,← Matrix.mul_assoc,unitary_left U hU,Matrix.one_mul]
end QSVTBlock

noncomputable section
open Matrix QSVT19.Main QAlgorithms
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTBlock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma alt_cons {n : ℕ} (U A B : Matrix ι ι ℂ) (Φ : Fin (n+1) → ℝ) :
    altPhaseSeq U A B Φ =
      (if n%2=0 then phaseRefl (Φ 0) B*U else phaseRefl (Φ 0) A*Uᴴ)*
        altPhaseSeq U A B (fun i : Fin n => Φ i.succ) := by
  unfold altPhaseSeq
  rw [List.ofFn_succ,List.prod_cons]
  simp only [Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero]
  congr 1
  congr 1
  congr 1
  funext i
  have hh : n-i.succ.val=n-1-i.val := by simp only [Fin.val_succ];omega
  rw [hh]
lemma refl_cons {n : ℕ} (Φ : Fin (n+1) → ℝ) (x : ℝ) :
    qspRefl Φ x = (qspZ (Φ 0)*reflR x)*qspRefl (fun i : Fin n => Φ i.succ) x := by
  simp [qspRefl,List.ofFn_succ]
lemma alt_lift (U A B : Matrix ι ι ℂ) (R L : Matrix ι (Fin 2) ℂ) (x : ℝ)
    (hu : U*R=L*reflR x) (hud : Uᴴ*L=R*reflR x)
    (ha : ∀ a : ℝ, phaseRefl a A*R=R*qspZ a)
    (hb : ∀ a : ℝ, phaseRefl a B*L=L*qspZ a) :
    ∀ n : ℕ, ∀ Φ : Fin n → ℝ, altPhaseSeq U A B Φ*R=
      if n%2=0 then R*qspRefl Φ x else L*qspRefl Φ x := by
  intro n
  induction n with
  | zero => intro Φ;simp [altPhaseSeq,qspRefl]
  | succ n ih =>
    intro Φ
    rw [alt_cons,Matrix.mul_assoc,ih,refl_cons]
    by_cases hn : n%2=0
    · have hn' : (n+1)%2≠0 := by omega
      simp only [hn,if_true,hn',if_false]
      have hs : (phaseRefl (Φ 0) B*U)*R=L*(qspZ (Φ 0)*reflR x) := by
        rw [Matrix.mul_assoc,hu,← Matrix.mul_assoc,hb,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc,hs,Matrix.mul_assoc]
    · have hn' : (n+1)%2=0 := by omega
      simp only [hn,if_false,hn',if_true]
      have hs : (phaseRefl (Φ 0) A*Uᴴ)*L=R*(qspZ (Φ 0)*reflR x) := by
        rw [Matrix.mul_assoc,hud,← Matrix.mul_assoc,ha,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc,hs,Matrix.mul_assoc]
lemma mul_pair_col (M : Matrix ι ι ℂ) (v w : ι → ℂ) : (M*pair v w).col 0=M*ᵥv := by
  funext i
  rfl
lemma phase_on_columns {U A B : Matrix ι ι ℂ} (S : ProjUnitarySVD U A B)
    (hU : U ∈ unitaryGroup ι ℂ) (hA : IsStarProjection A) (hB : IsStarProjection B)
    (n : ℕ) (Φ : Fin n → ℝ) (j : Fin S.d) :
    (n%2=0 → A*ᵥ(altPhaseSeq U A B Φ*ᵥS.ψ j)=qspRefl Φ (S.ςext j) 0 0 • S.ψ j) ∧
    (n%2≠0 → B*ᵥ(altPhaseSeq U A B Φ*ᵥS.ψ j)=qspRefl Φ (S.ςext j) 0 0 • leftVec S j) := by
  have hm := blocks S hU hB j
  have hh := alt_lift U A B (pair (S.ψ j) (rightRest S j)) (pair (leftVec S j) (leftRest S j)) (S.ςext j)
    hm.1 hm.2 (fun a => phase_vec A _ _ (P_fixed S j) (rightRest_null S hA hB j) a)
    (fun a => phase_vec B _ _ (left_fixed S j) (leftRest_null S j) a) n Φ
  constructor
  · intro hn
    rw [if_pos hn] at hh
    have hc := congrArg (fun M : Matrix ι (Fin 2) ℂ => A*ᵥM.col 0) hh
    rw [mul_pair_col,projected_pair A _ _ (P_fixed S j) (rightRest_null S hA hB j)] at hc
    exact hc
  · intro hn
    rw [if_neg hn] at hh
    have hc := congrArg (fun M : Matrix ι (Fin 2) ℂ => B*ᵥM.col 0) hh
    rw [mul_pair_col,projected_pair B _ _ (left_fixed S j) (leftRest_null S j)] at hc
    exact hc
end QSVTBlock

noncomputable section
open Matrix Polynomial QSVT19.Main
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTBlock
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma transform_frame {U A B : Matrix ι ι ℂ} (S : ProjUnitarySVD U A B) (M : Matrix ι ι ℂ)
    (f : Fin S.d → ι → ℂ) (h : ∀ j, M*ᵥS.ψ j=f j) :
    M*A=∑ j,vecMulVec (f j) (star (S.ψ j)) := by
  calc
    _ = M*(∑ j,vecMulVec (S.ψ j) (star (S.ψ j))) := congrArg (fun N : Matrix ι ι ℂ => M*N) S.span_ψ
    _ = _ := by simp only [Finset.mul_sum,mul_vecMulVec,h]
lemma odd_sum {U A B : Matrix ι ι ℂ} (S : ProjUnitarySVD U A B) (f : ℝ → ℂ) :
    svtOdd f S = ∑ j : Fin S.d, f (S.ςext j) • vecMulVec (leftVec S j) (star (S.ψ j)) := by
  unfold svtOdd
  apply Fintype.sum_of_injective (Fin.castLE (min_le_left S.d S.dt)) (Fin.castLE_injective _)
  · intro j hj
    have hn : ¬ j.val < min S.d S.dt := by
      intro hh;apply hj;exact ⟨⟨j.val,hh⟩,Fin.ext rfl⟩
    simp only [leftVec,dif_neg hn,zero_vecMulVec,smul_zero]
  · intro i
    simp only [ProjUnitarySVD.ςext,leftVec,Fin.val_castLE,dif_pos i.isLt,Fin.eta,ProjUnitarySVD.ψmin]
theorem theorem17_checked (U A B : Matrix ι ι ℂ) (hU : U ∈ unitaryGroup ι ℂ)
    (hA : IsStarProjection A) (hB : IsStarProjection B) (n : ℕ) (Φ : Fin n → ℝ) (P : ℂ[X])
    (hΦ : ∀ x ∈ Set.Icc (-1:ℝ) 1,qspRefl Φ x 0 0=P.eval (x:ℂ)) (S : ProjUnitarySVD U A B) :
    (Odd n → svtOdd (fun x => P.eval (x:ℂ)) S = B*altPhaseSeq U A B Φ*A) ∧
    (Even n → svtEven (fun x => P.eval (x:ℂ)) S = A*altPhaseSeq U A B Φ*A) := by
  have hx (j : Fin S.d) : S.ςext j ∈ Set.Icc (-1:ℝ) 1 :=
    ⟨by linarith [ext_nonneg S j],ext_le_one S hU hB j⟩
  constructor
  · intro hn
    have hm : n%2≠0 := by have hh := Nat.odd_iff.mp hn;omega
    have hc (j : Fin S.d) : (B*altPhaseSeq U A B Φ)*ᵥS.ψ j=P.eval (S.ςext j:ℂ) • leftVec S j := by
      rw [← mulVec_mulVec]
      have hh := (phase_on_columns S hU hA hB n Φ j).2 hm
      rw [hΦ _ (hx j)] at hh
      exact hh
    rw [odd_sum]
    have hh := transform_frame S (B*altPhaseSeq U A B Φ) _ hc
    simpa only [smul_vecMulVec] using hh.symm
  · intro hn
    have hm : n%2=0 := Nat.even_iff.mp hn
    have hc (j : Fin S.d) : (A*altPhaseSeq U A B Φ)*ᵥS.ψ j=P.eval (S.ςext j:ℂ) • S.ψ j := by
      rw [← mulVec_mulVec]
      have hh := (phase_on_columns S hU hA hB n Φ j).1 hm
      rw [hΦ _ (hx j)] at hh
      exact hh
    have hh := transform_frame S (A*altPhaseSeq U A B Φ) _ hc
    simpa only [svtEven,smul_vecMulVec] using hh.symm
end QSVTBlock

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Theorem 17, p. 18: "Let H_U be a finite-dimensional Hilbert space and let U, Π, Π̃ ∈
End(H_U) be linear operators on H_U such that U is a unitary, and Π, Π̃ are orthogonal projectors.
Let P ∈ C[x] and Φ ∈ R^n is as in Corollary 8, then
P^{(SV)}(Π̃UΠ) = Π̃U_ΦΠ if n is odd, and ΠU_ΦΠ if n is even. (32)"

**Formalization Note.** `H_U` is `ι → ℂ` for a finite type `ι`, with inner product
`star v ⬝ᵥ w`; `Π, Π̃` are `Proj, Projt`; "unitary" is `U ∈ Matrix.unitaryGroup ι ℂ` and
"orthogonal projector" is `IsStarProjection` (self-adjoint idempotent). "P and Φ as in Corollary 8" is read as (14): the top-left entry of
`∏_{j=1}^n e^{iφ_jσ_z}R(x)` is `P(x)` for every `x ∈ [−1, 1]`. That is the only property of `P`
and `Φ` the proof uses; Corollary 8's bullets on `P` are not assumed. `P^{(SV)}` is Definition
16 over an arbitrary singular value decomposition `S` of `Π̃UΠ` (`svtOdd` for odd `n`,
`svtEven` for even `n`, as in (32)); `U_Φ` is `altPhaseSeq` (Definition 15). No bound on `n` is
needed: at `n = 0`, (14) forces `P = 1` and both sides are `Π`. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (U Proj Projt : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hProj : IsStarProjection Proj) (hProjt : IsStarProjection Projt) (n : ℕ) (Φ : Fin n → ℝ) (P : ℂ[X]) (hΦ : ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspRefl Φ x 0 0 = P.eval (x : ℂ)) (S : ProjUnitarySVD U Proj Projt) :
    (Odd n → svtOdd (fun x => P.eval (x : ℂ)) S = Projt * altPhaseSeq U Proj Projt Φ * Proj) ∧ (Even n → svtEven (fun x => P.eval (x : ℂ)) S = Proj * altPhaseSeq U Proj Projt Φ * Proj) := by
  exact QSVTBlock.theorem17_checked U Proj Projt hU hProj hProjt n Φ P hΦ S