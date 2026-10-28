-- Prove2me | solution 1 for ProjRescale.MaxSupport.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:38:02.907537+00:00
-- url     : https://prove2.me/submissions/5b79ed78-bfa1-4e28-9131-644fc461a4a3

import Definitions.Def_ProjRescale_MaxSupport_Setting
import Init
import Mathlib


section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

def box (L : Submodule ℝ (E n)) : Set (E n) :=
  {x | x∈L ∧ x∈nonneg n ∧ ∀j,x j ≤ 1}

theorem zero_in_box (L : Submodule ℝ (E n)) : (0:E n)∈box L := by
  refine ⟨L.zero_mem,?_,?_⟩ <;> simp [nonneg]

theorem image_bounded (L : Submodule ℝ (E n)) (i : Fin n) :
    BddAbove ((fun x:E n=>x i) '' box L) := by
  refine ⟨1,?_⟩
  rintro z ⟨x,hx,rfl⟩
  exact hx.2.2 i

theorem image_nonempty (L : Submodule ℝ (E n)) (i : Fin n) :
    ((fun x:E n=>x i) '' box L).Nonempty :=
  ⟨0,0,zero_in_box L,by simp⟩

theorem sigma_bounds (L : Submodule ℝ (E n)) (i : Fin n) :
    0 ≤ sigmaI L i ∧ sigmaI L i ≤ 1 := by
  constructor
  · exact le_csSup (image_bounded L i) ⟨0,zero_in_box L,by simp⟩
  · apply csSup_le (image_nonempty L i)
    rintro z ⟨x,hx,rfl⟩
    exact hx.2.2 i

theorem normalized_positive_witness (L : Submodule ℝ (E n)) (i : Fin n)
    (x : E n) (hx : x∈L) (hn : x∈nonneg n) (hi : 0 < x i) :
    ∃y∈box L,0 < y i := by
  let M : ℝ:=1+∑j,x j
  have hsum : 0 ≤ ∑j,x j:=sum_nonneg (fun j _=>hn j)
  have hM : 0 < M:=by dsimp [M];linarith
  have hle (j : Fin n) : x j ≤ M := by
    have h:=single_le_sum (f:=fun k=>x k) (fun k _=>hn k) (mem_univ j)
    dsimp [M]
    linarith
  refine ⟨M⁻¹ • x,⟨L.smul_mem _ hx,?_,?_⟩,?_⟩
  · intro j
    simpa using mul_nonneg (inv_nonneg.mpr hM.le) (hn j)
  · intro j
    change M⁻¹*x j ≤ 1
    rw [mul_comm,←div_eq_mul_inv]
    exact (div_le_one hM).mpr (hle j)
  · simpa using mul_pos (inv_pos.mpr hM) hi

theorem mem_support_iff_sigma_pos (L : Submodule ℝ (E n)) (i : Fin n) :
    i∈maxSupp L ↔ 0 < sigmaI L i := by
  constructor
  · intro h
    obtain ⟨x,hx,hn,hi⟩:=(mem_filter.mp h).2
    obtain ⟨y,hy,hyi⟩:=normalized_positive_witness L i x hx hn hi
    exact hyi.trans_le (le_csSup (image_bounded L i) ⟨y,hy,rfl⟩)
  · intro hp
    by_contra hn
    have hle : sigmaI L i ≤ 0 := by
      apply csSup_le (image_nonempty L i)
      rintro z ⟨x,hx,rfl⟩
      apply le_of_not_gt
      intro hi
      exact hn (mem_filter.mpr ⟨mem_univ _,x,hx.1,hx.2.1,hi⟩)
    exact not_lt_of_ge hle hp

theorem sigma_observation (L : Submodule ℝ (E n)) :
    maxSupp L=univ.filter (fun i=>0 < sigmaI L i) ∧
      ∀h:(maxSupp L).Nonempty,condMeasure L=(maxSupp L).inf' h (sigmaI L) := by
  constructor
  · ext i
    simp only [mem_filter,mem_univ,true_and,mem_support_iff_sigma_pos]
  · intro h
    simp [condMeasure,h]

theorem condition_bounds (L : Submodule ℝ (E n)) : 0 < condMeasure L ∧ condMeasure L ≤ 1 := by
  unfold condMeasure
  split
  next h =>
    constructor
    · exact (lt_inf'_iff h).mpr (fun i hi=>(mem_support_iff_sigma_pos L i).mp hi)
    · obtain ⟨i,hi⟩:=h
      exact (inf'_le _ hi).trans (sigma_bounds L i).2
  next h => norm_num

theorem outside_support_zero (L : Submodule ℝ (E n)) (x : E n)
    (hx : x∈L) (hn : x∈nonneg n) (i : Fin n) (hi : i∉maxSupp L) : x i=0 := by
  apply le_antisymm _ (hn i)
  apply le_of_not_gt
  intro hp
  exact hi (mem_filter.mpr ⟨mem_univ _,x,hx,hn,hp⟩)
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport

def outerGuess (i : ℕ) : ℝ := (1/2)^(2^(i-1))

theorem outer_guess_pos (i : ℕ) : 0 < outerGuess i := pow_pos (by norm_num) _
theorem outer_guess_lt_one (i : ℕ) : outerGuess i < 1 :=
  pow_lt_one₀ (by norm_num) (by norm_num) (by positivity)
theorem outer_guess_one : outerGuess 1=1/2 := by norm_num [outerGuess]
theorem outer_guess_next (i : ℕ) (hi : 1 ≤ i) : outerGuess (i+1)=outerGuess i^2 := by
  have he : 2^i=2^(i-1)*2 := by
    conv_lhs => rw [show i=(i-1)+1 by omega]
    exact pow_succ _ _
  simp only [outerGuess,Nat.add_sub_cancel,he,pow_mul]

theorem reciprocal_outer_guess (i : ℕ) : 1/outerGuess i=(2:ℝ)^(2^(i-1)) := by
  simp [outerGuess,one_div_pow]

theorem outer_guess_log (i : ℕ) : ⌊Real.logb 2 (1/outerGuess i)⌋₊=2^(i-1) := by
  rw [reciprocal_outer_guess,Real.logb_pow,show Real.logb 2 2=1 by norm_num,mul_one]
  exact Nat.floor_natCast _

theorem outer_guess_at_k (m : ℝ) (hm : 0 < m) (hm1 : m ≤ 1) :
    outerGuess (kIter m) ≤ m := by
  have hk : 1 ≤ kIter m := le_max_left _ _
  have hg : outerGuess (kIter m) ≤ 1/2 := by
    have he : 2^(kIter m-1) = (2^(kIter m-1)-1)+1 := by
      have : 0 < 2^(kIter m-1) := by positivity
      omega
    unfold outerGuess
    rw [he,pow_succ]
    have hp : (1/2:ℝ)^(2^(kIter m-1)-1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  by_cases hhalf : 1/2 ≤ m
  · exact hg.trans hhalf
  have hinv : 1 < 1/m := (one_lt_div hm).mpr (by linarith)
  have hlog : 0 < Real.logb 2 (1/m) := (Real.logb_pos_iff (by norm_num) (by positivity)).mpr hinv
  have hc : ⌈Real.logb 2 (Real.logb 2 (1/m))⌉ ≤ ((kIter m-1:ℕ):ℤ) := by
    have h1 := Int.self_le_toNat (⌈Real.logb 2 (Real.logb 2 (1/m))⌉+1)
    have h2 : (⌈Real.logb 2 (Real.logb 2 (1/m))⌉+1).toNat ≤ kIter m := le_max_right _ _
    omega
  have ht : Real.logb 2 (Real.logb 2 (1/m)) ≤ ((kIter m-1:ℕ):ℝ) :=
    (Int.le_ceil _).trans (by exact_mod_cast hc)
  have hpow : Real.logb 2 (1/m) ≤ (2:ℝ)^(kIter m-1) := by
    rw [←Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num) hlog).mp ht
  have hpow' : Real.logb 2 (1/m) ≤ ((2^(kIter m-1):ℕ):ℝ) := by exact_mod_cast hpow
  have hbound : 1/m ≤ (2:ℝ)^(2^(kIter m-1)) := by
    rw [←Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).mp hpow'
  have hrec := reciprocal_outer_guess (kIter m)
  rw [←hrec] at hbound
  exact (one_div_le_one_div hm (outer_guess_pos _)).mp hbound

def outerSpent (n t : ℕ) : ℕ := ∑j∈range t,2*n*(2^j+1)
def outerCap (n i : ℕ) : ℕ := n*(2^(i-1)+1)
theorem outer_spent_zero (n : ℕ) : outerSpent n 0=0 := by simp [outerSpent]
theorem outer_spent_succ (n t : ℕ) : outerSpent n (t+1)=outerSpent n t+2*n*(2^t+1) := by
  simp [outerSpent,sum_range_succ]
theorem outer_spent_step (n i : ℕ) (hi : 1 ≤ i) :
    outerSpent n i=outerSpent n (i-1)+2*outerCap n i := by
  conv_lhs => rw [show i=(i-1)+1 by omega,outer_spent_succ]
  simp [outerCap,mul_assoc]
theorem outer_spent_mono (n : ℕ) : Monotone (outerSpent n) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [outer_spent_succ]
  omega
theorem outer_spent_closed (n k : ℕ) : outerSpent n k=2*n*(2^k-1+k) := by
  induction k with
  | zero => simp [outerSpent]
  | succ k ih =>
    rw [outer_spent_succ,ih,pow_succ]
    have hp : 1 ≤ 2^k := Nat.one_le_pow _ _ (by norm_num)
    have he : 2^k*2-1+(k+1)=(2^k-1+k)+(2^k+1) := by omega
    rw [he]
    ring
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
open scoped InnerProductSpace
variable {n : ℕ}

theorem coordinate_sum {α : Type*} (S : Finset α) (f : α → E n) (j : Fin n) :
    (∑i∈S,f i) j=∑i∈S,f i j := by
  exact map_sum (PiLp.projₗ (p:=2) (𝕜:=ℝ) (fun _ : Fin n=>ℝ) j) f S

theorem maximum_support_point_exists (L : Submodule ℝ (E n)) :
    ∃x,IsMaxSupportPoint L x := by
  have hchoice : ∀i:Fin n,∃x:E n,x∈L ∧ x∈nonneg n ∧ (i∈maxSupp L → 0 < x i) := by
    intro i
    by_cases hi : i∈maxSupp L
    · obtain ⟨x,hx,hn,hp⟩:=(mem_filter.mp hi).2
      exact ⟨x,hx,hn,fun _=>hp⟩
    · exact ⟨0,L.zero_mem,by simp [nonneg],fun h=>False.elim (hi h)⟩
  choose x hx hn hp using hchoice
  let y : E n:=∑i,x i
  have hyL : y∈L:=L.sum_mem (fun i _=>hx i)
  have hyn : y∈nonneg n := by
    intro j
    rw [show y j=∑i,x i j from coordinate_sum _ _ _]
    exact sum_nonneg (fun i _=>hn i j)
  refine ⟨y,hyL,hyn,?_⟩
  intro j
  constructor
  · intro hj
    exact mem_filter.mpr ⟨mem_univ _,y,hyL,hyn,hj⟩
  · intro hj
    have h : x j j ≤ y j := by
      rw [show y j=∑i,x i j from coordinate_sum _ _ _]
      exact single_le_sum (fun i _=>hn i j) (mem_univ _)
    exact (hp j hj).trans_le h

theorem orthogonal_nonneg_coordinate_product (L : Submodule ℝ (E n))
    (x y : E n) (hx : x∈L) (hy : y∈Lᗮ) (hxn : x∈nonneg n) (hyn : y∈nonneg n)
    (i : Fin n) : x i*y i=0 := by
  have hinner : ⟪x,y⟫_ℝ=0:=Submodule.inner_right_of_mem_orthogonal hx hy
  have hs : ∑j,y j*x j=0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct] using hinner
  have hi : y i*x i ≤ ∑j,y j*x j:=single_le_sum (fun j _=>mul_nonneg (hyn j) (hxn j)) (mem_univ _)
  rw [hs] at hi
  have h0:=mul_nonneg (hxn i) (hyn i)
  nlinarith

theorem support_disjoint (L : Submodule ℝ (E n)) : Disjoint (maxSupp L) (maxSupp Lᗮ) := by
  apply disjoint_left.mpr
  intro i hi hj
  obtain ⟨x,hx,hn,hxi⟩:=(mem_filter.mp hi).2
  obtain ⟨y,hy,hyn,hyi⟩:=(mem_filter.mp hj).2
  have he:=orthogonal_nonneg_coordinate_product L x y hx hy hn hyn i
  exact (ne_of_gt (mul_pos hxi hyi)) he

theorem covering_partial_supports (L : Submodule ℝ (E n)) (J K : Finset (Fin n))
    (hJ : J⊆maxSupp L) (hK : K⊆maxSupp Lᗮ) (hcov : J∪K=univ) :
    J=maxSupp L ∧ K=maxSupp Lᗮ := by
  have hd:=support_disjoint L
  constructor
  · apply Subset.antisymm hJ
    intro i hi
    have hc : i∈J∪K:=by rw [hcov];exact mem_univ _
    rcases mem_union.mp hc with h|h
    · exact h
    · exact False.elim (disjoint_left.mp hd hi (hK h))
  · apply Subset.antisymm hK
    intro i hi
    have hc : i∈J∪K:=by rw [hcov];exact mem_univ _
    rcases mem_union.mp hc with h|h
    · exact False.elim (disjoint_left.mp hd (hJ h) hi)
    · exact h
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

theorem diagonal_apply (d : Fin n → ℝ) (x : E n) (i : Fin n) :
    Matrix.toEuclideanLin (Matrix.diagonal d) x i=d i*x i := by
  simp [Matrix.toEuclideanLin_apply,Matrix.mulVec_diagonal]

def outputGood (L : Submodule ℝ (E n)) (x : E n) (J : Finset (Fin n)) : Prop :=
  x∈L ∧ x∈nonneg n ∧ ∀j,0 < x j ↔ j∈J

theorem zero_output (L : Submodule ℝ (E n)) : outputGood L 0 ∅ := by
  refine ⟨L.zero_mem,?_,?_⟩ <;> simp [nonneg]

theorem output_support_subset (L : Submodule ℝ (E n)) (x : E n) (J : Finset (Fin n))
    (h : outputGood L x J) : J⊆maxSupp L := by
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _,x,h.1,h.2.1,(h.2.2 i).mpr hi⟩

theorem inverse_diagonal_mem (L : Submodule ℝ (E n)) (d : Fin n → ℝ)
    (hd : ∀i,0 < d i) (y : E n) (hy : y∈diagScale d L) :
    WithLp.toLp 2 (fun i=>(d i)⁻¹*y i)∈L := by
  obtain ⟨x,hx,he⟩:=Submodule.mem_map.mp hy
  have hv : WithLp.toLp 2 (fun i=>(d i)⁻¹*y i)=x := by
    ext i
    have hi : d i*x i=y i:=by simpa only [diagonal_apply] using congrArg (fun v:E n=>v i) he
    change (d i)⁻¹*y i=x i
    rw [←hi,inv_mul_cancel_left₀ (ne_of_gt (hd i))]
  rwa [hv]

theorem found_output (L : Submodule ℝ (E n)) (d : Fin n → ℝ) (hd : ∀i,0 < d i)
    (J : Finset (Fin n)) (u : E n) (hp : ∀j∈J,0 < projDLJ L d J u j) :
    outputGood L (WithLp.toLp 2 (fun i=>(d i)⁻¹*projDLJ L d J u i)) J := by
  have hproj : projDLJ L d J u∈diagScale d L ⊓ coordSub J :=
    (diagScale d L ⊓ coordSub J).starProjection_apply_mem u
  have hz (i : Fin n) (hi : i∉J) : projDLJ L d J u i=0:=hproj.2 i hi
  have hpos (i : Fin n) (hi : i∈J) : 0 < (d i)⁻¹*projDLJ L d J u i :=
    mul_pos (inv_pos.mpr (hd i)) (hp i hi)
  refine ⟨inverse_diagonal_mem L d hd _ hproj.1,?_,?_⟩
  · intro i
    change 0 ≤ (d i)⁻¹*projDLJ L d J u i
    by_cases hi : i∈J
    · exact (hpos i hi).le
    · rw [hz i hi,mul_zero]
  · intro i
    change 0 < (d i)⁻¹*projDLJ L d J u i ↔ i∈J
    by_cases hi : i∈J
    · exact ⟨fun _=>hi,fun _=>hpos i hi⟩
    · simp [hi,hz i hi]

def a1Invariant (L : Submodule ℝ (E n)) : A1State n → Prop
  | .run d _ _ => ∀i,0 < d i
  | .halt x J _ => outputGood L x J

theorem a1_step_preserves (L : Submodule ℝ (E n)) (σ : ℝ) {s t : A1State n}
    (h : A1Step L σ s t) (hs : a1Invariant L s) : a1Invariant L t := by
  cases h with
  | found d J r u hu hp => exact found_output L d hs J u hp
  | rescale d J r z i hz hi hc =>
    have hd : ∀j,0 < Function.update d i (2*d i) j := by
      intro j
      by_cases hj : j=i
      · subst j
        simp only [Function.update_self]
        exact mul_pos (by norm_num) (hs i)
      · simpa only [Function.update_of_ne hj] using hs j
    unfold rescaleNext
    dsimp only
    split <;> split
    · exact zero_output L
    · exact hd
    · exact zero_output L
    · exact hd

theorem a1_reachable_invariant (L : Submodule ℝ (E n)) (σ : ℝ) (s : A1State n)
    (h : Relation.ReflTransGen (A1Step L σ) (A1Init n) s) : a1Invariant L s := by
  induction h with
  | refl => intro i;norm_num [A1Init]
  | tail h hs ih => exact a1_step_preserves L σ hs ih

theorem halting_output_good (L : Submodule ℝ (E n)) (σ : ℝ) (x : E n)
    (J : Finset (Fin n)) (r : ℕ) (h : A1Halts L σ x J r) : outputGood L x J :=
  a1_reachable_invariant L σ (.halt x J r) h

theorem covering_halts_maximal (L : Submodule ℝ (E n)) (σ : ℝ)
    (x xh : E n) (J Jh : Finset (Fin n)) (r rh : ℕ)
    (hx : A1Halts L σ x J r) (hxh : A1Halts Lᗮ σ xh Jh rh) (hcov : J∪Jh=univ) :
    J=maxSupp L ∧ Jh=maxSupp Lᗮ ∧ IsMaxSupportPoint L x ∧ IsMaxSupportPoint Lᗮ xh := by
  have h:=halting_output_good L σ x J r hx
  have hh:=halting_output_good Lᗮ σ xh Jh rh hxh
  have he:=covering_partial_supports L J Jh (output_support_subset L x J h)
    (output_support_subset Lᗮ xh Jh hh) hcov
  exact ⟨he.1,he.2,⟨h.1,h.2.1,by simpa only [←he.1] using h.2.2⟩,
    ⟨hh.1,hh.2.1,by simpa only [←he.2] using hh.2.2⟩⟩
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
open scoped InnerProductSpace
variable {n : ℕ}

theorem abs_coordinate_le_sup (x : E n) (i : Fin n) : |x i| ≤ supNorm x :=
  by
    change |x i| ≤ ⨆j,|x j|
    exact le_ciSup (Set.finite_range (fun j=>|x j|)).bddAbove i

theorem nonneg_coordinate_le_sup (x : E n) (hx : x∈nonneg n) (i : Fin n) : x i ≤ supNorm x := by
  simpa only [abs_of_nonneg (hx i)] using abs_coordinate_le_sup x i

theorem sup_positive (x : E n) (hx : x≠0) : 0 < supNorm x := by
  by_contra hn
  have hle : supNorm x ≤ 0:=le_of_not_gt hn
  apply hx
  ext i
  have h:= (abs_coordinate_le_sup x i).trans hle
  simpa [abs_nonpos_iff] using h

theorem box_sup_le_one (L : Submodule ℝ (E n)) (x : E n) (hx : x∈box L)
    (i : Fin n) : supNorm x ≤ 1 := by
  letI : Nonempty (Fin n):=⟨i⟩
  apply ciSup_le
  intro j
  simpa only [abs_of_nonneg (hx.2.1 j)] using hx.2.2 j

theorem projection_inner_identity (L : Submodule ℝ (E n)) (x z : E n) (hx : x∈L) :
    (∑j,x j*z j)=∑j,x j*(L.starProjection z) j := by
  have h:=Submodule.inner_right_of_mem_orthogonal hx (L.sub_starProjection_mem_orthogonal z)
  rw [inner_sub_right] at h
  have he : ⟪x,z⟫_ℝ=⟪x,L.starProjection z⟫_ℝ:=sub_eq_zero.mp h
  simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm] using he

theorem certificate_half_bound (L : Submodule ℝ (E n)) (z : E n) (i : Fin n)
    (hz : z∈nonneg n) (hz0 : z≠0) (hzi : supNorm z=z i)
    (hP : posL1 (L.starProjection z) ≤ supNorm z/2) :
    ∀x∈L,x∈nonneg n → x i ≤ supNorm x/2 := by
  intro x hx hn
  have hzi0 : 0 < z i:=by rw [←hzi];exact sup_positive z hz0
  have hx0 : 0 ≤ supNorm x:=(abs_nonneg (x i)).trans (abs_coordinate_le_sup x i)
  have hstart : x i*z i ≤ ∑j,x j*z j := single_le_sum (fun j _=>mul_nonneg (hn j) (hz j)) (mem_univ _)
  have hbound : (∑j,x j*(L.starProjection z) j) ≤ supNorm x*posL1 (L.starProjection z) := by
    unfold posL1
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    calc
      _ ≤ x j*max ((L.starProjection z) j) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) (hn j)
      _ ≤ _ := mul_le_mul_of_nonneg_right (nonneg_coordinate_le_sup x hn j) (le_max_right _ _)
  rw [projection_inner_identity L x z hx] at hstart
  have hlast:=mul_le_mul_of_nonneg_left hP hx0
  rw [hzi] at hlast
  have hm : x i*z i ≤ (supNorm x/2)*z i := by nlinarith
  exact (mul_le_mul_iff_left₀ hzi0).mp (by simpa only [mul_comm] using hm)
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
open scoped InnerProductSpace
variable {n : ℕ}

/-- A maximum-support point absorbs arbitrary negative coordinates on its support. -/
theorem extend_nonnegative (L : Submodule ℝ (E n)) (x : E n) (hx : x∈L)
    (hn : ∀j,j∉maxSupp L → 0≤x j) :
    ∃y∈L,y∈nonneg n ∧ ∀j,j∉maxSupp L → y j=x j := by
  obtain ⟨u,hu,hun,hup⟩:=maximum_support_point_exists L
  let t : ℝ:=∑j∈maxSupp L,max 0 (-x j/u j)
  have ht : 0≤t:=sum_nonneg (fun j _=>le_max_left _ _)
  refine ⟨x+t•u,L.add_mem hx (L.smul_mem t hu),?_,?_⟩
  · intro j
    change 0≤x j+t*u j
    by_cases hj : j∈maxSupp L
    · have huj:= (hup j).mpr hj
      have hle : -x j/u j≤t:= (le_max_right _ _).trans
        (single_le_sum (fun k _=>le_max_left 0 (-x k/u k)) hj)
      have := (div_le_iff₀ huj).mp hle
      linarith
    · exact add_nonneg (hn j hj) (mul_nonneg ht (hun j))
  · intro j hj
    have hz:=outside_support_zero L u hu hun j hj
    change x j+t*u j=x j
    simp [hz]

theorem outside_nonnegative_zero (L : Submodule ℝ (E n)) (x : E n) (hx : x∈L)
    (hn : ∀j,j∉maxSupp L → 0≤x j) (j : Fin n) (hj : j∉maxSupp L) : x j=0 := by
  obtain ⟨y,hy,hyn,he⟩:=extend_nonnegative L x hx hn
  rw [←he j hj]
  exact outside_support_zero L y hy hyn j hj

theorem simplex_convex (J : Finset (Fin n)) : Convex ℝ (simplexJ J) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_,?_,?_⟩
  · intro j
    change 0≤a*x j+b*y j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · intro j hj
    change a*x j+b*y j=0
    simp [hx.2.1 j hj,hy.2.1 j hj]
  · change ∑j,(a*x j+b*y j)=1
    rw [sum_add_distrib,←mul_sum,←mul_sum,hx.2.2,hy.2.2]
    simpa using hab

theorem single_in_simplex (J : Finset (Fin n)) (j : Fin n) (hj : j∈J) :
    EuclideanSpace.single j (1:ℝ)∈simplexJ J := by
  refine ⟨?_,?_,?_⟩
  · intro k
    simp only [EuclideanSpace.single_apply]
    split <;> norm_num
  · intro k hk
    have hkj : k≠j:=fun h=>hk (h ▸ hj)
    simp [EuclideanSpace.single_apply,hkj]
  · simp [EuclideanSpace.single_apply]

theorem single_in_coord (J : Finset (Fin n)) (j : Fin n) (hj : j∈J) :
    EuclideanSpace.single j (1:ℝ)∈coordSub J := by
  intro k hk
  have hkj : k≠j:=fun h=>hk (h ▸ hj)
  simp [EuclideanSpace.single_apply,hkj]

theorem functional_zero_of_upper_bound (K : Submodule ℝ (E n))
    (f : StrongDual ℝ (E n)) (a : ℝ) (hf : ∀x∈K,f x<a) : ∀x∈K,f x=0 := by
  intro x hx
  by_contra h
  have hb:=hf (((a+1)/f x) • x) (K.smul_mem _ hx)
  rw [map_smul] at hb
  change ((a+1)/f x)*f x<a at hb
  rw [div_mul_cancel₀ _ h] at hb
  linarith

theorem complement_support_witness (L : Submodule ℝ (E n)) :
    ∃y∈Lᗮ,y∈nonneg n ∧ ∀j,j∉maxSupp L → 0<y j := by
  let S:=maxSupp L
  let J:=Sᶜ
  let K : Submodule ℝ (E n):=L⊔coordSub S
  let B : Set (E n):=(fun j:Fin n=>EuclideanSpace.single j (1:ℝ)) '' (↑J : Set (Fin n))
  let C:=convexHull ℝ B
  have hC : C⊆simplexJ J:=convexHull_min (by
    rintro _ ⟨j,hj,rfl⟩
    exact single_in_simplex J j hj) (simplex_convex J)
  have hdis : Disjoint (↑K:Set (E n)) C := by
    apply Set.disjoint_left.mpr
    intro z hz hc
    have hzS:=hC hc
    obtain ⟨x,hx,v,hv,rfl⟩:=Submodule.mem_sup.mp hz
    have hxn : ∀j,j∉S → 0≤x j := by
      intro j hj
      have h:=hzS.1 j
      change 0≤x j+v j at h
      have hvj : v j=0:=hv j hj
      simpa [hvj] using h
    have hz0 : x+v=0 := by
      ext j
      by_cases hj : j∈S
      · exact hzS.2.1 j (by simpa [J] using hj)
      · change x j+v j=0
        rw [hv j hj,outside_nonnegative_zero L x hx hxn j hj]
        simp
    have hh:=hzS.2.2
    rw [hz0] at hh
    simpa using hh
  obtain ⟨f,a,b,hfa,hab,hfb⟩:=geometric_hahn_banach_closed_compact
    K.convex K.closed_of_finiteDimensional (convex_convexHull ℝ B)
    ((J.finite_toSet.image _).isCompact_convexHull ℝ) hdis
  have hf0:=functional_zero_of_upper_bound K f a hfa
  have ha : 0<a:=by simpa using hfa 0 K.zero_mem
  let y: E n:=(InnerProductSpace.toDual ℝ (E n)).symm f
  have hfy (j:Fin n) : y j=f (EuclideanSpace.single j (1:ℝ)) := by
    have h:=InnerProductSpace.toDual_symm_apply (x:=EuclideanSpace.single j (1:ℝ)) (y:=f)
    simpa only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] using h
  have hyp (j:Fin n) (hj:j∉S) : 0<y j := by
    rw [hfy]
    have hm : EuclideanSpace.single j (1:ℝ)∈C:=subset_convexHull ℝ B ⟨j,by simpa [J] using hj,rfl⟩
    exact ha.trans (hab.trans (hfb _ hm))
  refine ⟨y,?_,?_,hyp⟩
  · apply (L.mem_orthogonal' y).mpr
    intro x hx
    rw [show ⟪y,x⟫_ℝ=f x from InnerProductSpace.toDual_symm_apply]
    exact hf0 x (Submodule.mem_sup_left hx)
  · intro j
    by_cases hj:j∈S
    · rw [hfy,hf0 _ (Submodule.mem_sup_right (single_in_coord S j hj))]
    · exact (hyp j hj).le

theorem support_partition (L : Submodule ℝ (E n)) :
    maxSupp L∩maxSupp Lᗮ=∅ ∧ maxSupp L∪maxSupp Lᗮ=univ := by
  refine ⟨disjoint_iff_inter_eq_empty.mp (support_disjoint L),?_⟩
  apply eq_univ_of_forall
  intro j
  by_cases hj:j∈maxSupp L
  · exact mem_union_left _ hj
  · obtain ⟨y,hy,hyn,hyp⟩:=complement_support_witness L
    exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,y,hy,hyn,hyp j hj⟩)
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

theorem diagonal_box_image (L : Submodule ℝ (E n)) (d : Fin n → ℝ)
    (hd : ∀i,1 ≤ d i) (hf : ∀x∈box L,∀i,d i*x i ≤ 1) :
    (Matrix.toEuclideanLin (Matrix.diagonal d)) '' box L=box (diagScale d L) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨Submodule.mem_map.mpr ⟨x,hx.1,rfl⟩,?_,?_⟩
    · intro i
      rw [diagonal_apply]
      exact mul_nonneg (le_trans (by norm_num) (hd i)) (hx.2.1 i)
    · intro i
      rw [diagonal_apply]
      exact hf x hx i
  · intro hy
    obtain ⟨x,hx,he⟩:=Submodule.mem_map.mp hy.1
    have hc (i : Fin n) : d i*x i=y i := by
      simpa only [diagonal_apply] using congrArg (fun v:E n=>v i) he
    have hn : x∈nonneg n := by
      intro i
      have hh : 0 ≤ d i*x i:=by rw [hc];exact hy.2.1 i
      exact nonneg_of_mul_nonneg_right hh (by linarith [hd i])
    have hb : ∀i,x i ≤ 1 := by
      intro i
      calc
        x i = 1*x i := by ring
        _ ≤ d i*x i := mul_le_mul_of_nonneg_right (hd i) (hn i)
        _ = y i := hc i
        _ ≤ 1 := hy.2.2 i
    exact ⟨x,⟨hx,hn,hb⟩,he⟩

theorem sigma_diagonal_transport (L : Submodule ℝ (E n)) (d : Fin n → ℝ)
    (hd : ∀i,1 ≤ d i) (hf : ∀x∈box L,∀i,d i*x i ≤ 1) (j : Fin n) :
    sigmaI (diagScale d L) j=d j*sigmaI L j := by
  have he:=diagonal_box_image L d hd hf
  have hdj : 0 < d j:=lt_of_lt_of_le (by norm_num) (hd j)
  apply le_antisymm
  · apply csSup_le (image_nonempty (diagScale d L) j)
    rintro z ⟨y,hy,rfl⟩
    rw [←he] at hy
    obtain ⟨x,hx,rfl⟩:=hy
    dsimp only
    rw [diagonal_apply]
    exact mul_le_mul_of_nonneg_left (le_csSup (image_bounded L j) ⟨x,hx,rfl⟩) hdj.le
  · have hs : sigmaI L j ≤ sigmaI (diagScale d L) j/d j := by
      apply csSup_le (image_nonempty L j)
      rintro z ⟨x,hx,rfl⟩
      apply (le_div_iff₀ hdj).mpr
      have hy : Matrix.toEuclideanLin (Matrix.diagonal d) x∈box (diagScale d L) := by
        rw [←he]
        exact ⟨x,hx,rfl⟩
      have hb:=le_csSup (image_bounded (diagScale d L) j) ⟨_,hy,rfl⟩
      simpa only [diagonal_apply,mul_comm,sigmaI,box] using hb
    have hh:=(le_div_iff₀ hdj).mp hs
    simpa only [mul_comm] using hh

theorem rescaling_lemma (L : Submodule ℝ (E n)) (z : E n) (i : Fin n)
    (hz : z∈nonneg n) (hz0 : z≠0) (hzi : supNorm z=z i)
    (hP : posL1 (L.starProjection z) ≤ supNorm z/2) :
    (∀x∈L,x∈nonneg n → x i ≤ supNorm x/2) ∧
      sigmaI (diagScale (Function.update (fun _=>1) i 2) L) i=2*sigmaI L i ∧
      ∀j,j≠i → sigmaI (diagScale (Function.update (fun _=>1) i 2) L) j=sigmaI L j := by
  have hhalf:=certificate_half_bound L z i hz hz0 hzi hP
  let d : Fin n → ℝ:=Function.update (fun _=>1) i 2
  have hd : ∀j,1 ≤ d j := by
    intro j
    by_cases h : j=i <;> simp [d,h]
  have hf : ∀x∈box L,∀j,d j*x j ≤ 1 := by
    intro x hx j
    by_cases hj : j=i
    · subst j
      simp only [d,Function.update_self]
      have hh:=hhalf x hx.1 hx.2.1
      have hs:=box_sup_le_one L x hx i
      linarith
    · simpa only [d,Function.update_of_ne hj,one_mul] using hx.2.2 j
  refine ⟨hhalf,?_,?_⟩
  · simpa only [d,Function.update_self] using sigma_diagonal_transport L d hd hf i
  · intro j hj
    simpa only [d,Function.update_of_ne hj,one_mul] using sigma_diagonal_transport L d hd hf j
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
open scoped InnerProductSpace
variable {n : ℕ}

theorem positive_sum_of_coordinate (x : E n) (hx : x∈nonneg n) (i : Fin n)
    (hi : 0<x i) : 0<∑j,x j :=
  hi.trans_le (single_le_sum (fun j _=>hx j) (mem_univ i))

theorem normalized_simplex (x : E n) (J : Finset (Fin n)) (hx : x∈nonneg n)
    (hs : ∀j,j∉J → x j=0) (ht : 0<∑j,x j) :
    (∑j,x j)⁻¹ • x∈simplexJ J := by
  refine ⟨?_,?_,?_⟩
  · intro j
    change 0≤(∑j,x j)⁻¹*x j
    exact mul_nonneg (inv_nonneg.mpr ht.le) (hx j)
  · intro j hj
    change (∑j,x j)⁻¹*x j=0
    rw [hs j hj,mul_zero]
  · change (∑j,(∑k,x k)⁻¹*x j)=1
    rw [←mul_sum,inv_mul_cancel₀ (ne_of_gt ht)]

theorem restrict_orthogonal (K : Submodule ℝ (E n)) (J : Finset (Fin n))
    (hK : K≤coordSub J) (y : E n) (hy : y∈Kᗮ) :
    WithLp.toLp 2 (fun j=>if j∈J then y j else 0)∈Kᗮ := by
  apply (K.mem_orthogonal _).mpr
  intro x hx
  have h:= (K.mem_orthogonal y).mp hy x hx
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h ⊢
  simp only [dotProduct,star_trivial] at h ⊢
  calc
    _ = ∑j,y j*x j := by
      apply sum_congr rfl
      intro j _
      by_cases hj:j∈J
      · simp [hj]
      · have hz:=hK hx j hj
        simp [hj,hz]
    _ = 0 := h

/-- Exact alternative stronger than the basic procedure's approximate certificate. -/
theorem basic_alternative (K : Submodule ℝ (E n)) (J : Finset (Fin n))
    (hK : K≤coordSub J) (hJ : J.Nonempty) :
    (∃u∈simplexJ J,∀j∈J,0<K.starProjection u j) ∨
    (∃z∈simplexJ J,K.starProjection z=0) := by
  by_cases hcov : J⊆maxSupp K
  · obtain ⟨x,hx,hxn,hxp⟩:=maximum_support_point_exists K
    obtain ⟨i,hi⟩:=hJ
    have ht:=positive_sum_of_coordinate x hxn i ((hxp i).mpr (hcov hi))
    let u: E n:=(∑j,x j)⁻¹•x
    have hu : u∈K:=K.smul_mem _ hx
    have hpu : K.starProjection u=u:=K.starProjection_eq_self_iff.mpr hu
    refine Or.inl ⟨u,normalized_simplex x J hxn (hK hx) ht,?_⟩
    intro j hj
    rw [hpu]
    change 0<(∑k,x k)⁻¹*x j
    exact mul_pos (inv_pos.mpr ht) ((hxp j).mpr (hcov hj))
  · obtain ⟨i,hi,hni⟩:=not_subset.mp hcov
    obtain ⟨y,hy,hyn,hyp⟩:=complement_support_witness K
    let w : E n:=WithLp.toLp 2 (fun j=>if j∈J then y j else 0)
    have hwn : w∈nonneg n := by
      intro j
      dsimp [w]
      split
      · exact hyn j
      · exact le_rfl
    have hws : ∀j,j∉J → w j=0 := by intro j hj;simp [w,hj]
    have hwi : 0<w i:=by simpa [w,hi] using hyp i hni
    have ht:=positive_sum_of_coordinate w hwn i hwi
    let z : E n:=(∑j,w j)⁻¹•w
    have hzo : z∈Kᗮ:=Kᗮ.smul_mem _ (restrict_orthogonal K J hK y hy)
    have hz0 : K.starProjection z=0 := by
      apply K.eq_starProjection_of_mem_orthogonal K.zero_mem
      simpa using hzo
    exact Or.inr ⟨z,normalized_simplex w J hwn hws ht,hz0⟩

theorem simplex_argmax (J : Finset (Fin n)) (hJ : J.Nonempty) (z : E n) :
    ∃i:Fin n,∀j,z j≤z i := by
  have hn : (univ:Finset (Fin n)).Nonempty:=hJ.mono (subset_univ _)
  obtain ⟨i,_,hi⟩:=exists_max_image univ (fun j=>z j) hn
  exact ⟨i,fun j=>hi j (mem_univ _)⟩

theorem running_has_step (L : Submodule ℝ (E n)) (σ : ℝ)
    (d : Fin n→ℝ) (J : Finset (Fin n)) (r : ℕ) (hJ : J.Nonempty) :
    ∃s,A1Step L σ (.run d J r) s := by
  let K:=diagScale d L⊓coordSub J
  rcases basic_alternative K J inf_le_right hJ with ⟨u,hu,hp⟩|⟨z,hz,hp⟩
  · exact ⟨_,A1Step.found d J r u hu hp⟩
  · obtain ⟨i,hi⟩:=simplex_argmax J hJ z
    refine ⟨_,A1Step.rescale d J r z i hz hi ?_⟩
    change posL1 (K.starProjection z) ≤ supNorm z/2
    rw [hp]
    have h0 : 0≤ supNorm z:=(abs_nonneg (z i)).trans (abs_coordinate_le_sup z i)
    simpa [posL1] using (div_nonneg h0 (by norm_num : (0:ℝ)≤2))

def runningNonempty : A1State n → Prop
  | .run _ J _ => J.Nonempty
  | .halt _ _ _ => True

theorem running_nonempty_step (L : Submodule ℝ (E n)) (σ : ℝ) {s t : A1State n}
    (h : A1Step L σ s t) : runningNonempty t := by
  cases h with
  | found => trivial
  | rescale d J r z i hz hi hc =>
    unfold rescaleNext
    dsimp only
    split <;> split
    · trivial
    · exact nonempty_iff_ne_empty.mpr (by assumption)
    · trivial
    · exact nonempty_iff_ne_empty.mpr (by assumption)

theorem reachable_running_nonempty (hn : 0<n) (L : Submodule ℝ (E n)) (σ : ℝ)
    (s : A1State n) (h : Relation.ReflTransGen (A1Step L σ) (A1Init n) s) :
    runningNonempty s := by
  induction h with
  | refl => exact ⟨⟨0,hn⟩,mem_univ _⟩
  | tail h hs ih => exact running_nonempty_step L σ hs

theorem a1_never_stuck (hn : 0<n) (L : Submodule ℝ (E n)) (σ : ℝ)
    (s : A1State n) (h : Relation.ReflTransGen (A1Step L σ) (A1Init n) s)
    (hr : s.IsRun) : ∃s',A1Step L σ s s' := by
  cases s with
  | run d J r => exact running_has_step L σ d J r (reachable_running_nonempty hn L σ _ h)
  | halt x J r => exact False.elim hr
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling.Controls
open Finset Classical ProjRescale.MaxSupport

theorem zero_space_sigma {n : ℕ} (i : Fin n) : sigmaI (⊥:Submodule ℝ (E n)) i=0 := by
  apply le_antisymm _ (sigma_bounds _ i).1
  apply csSup_le (image_nonempty _ i)
  rintro z ⟨x,hx,rfl⟩
  have hx0 : x=0:=by simpa only [Submodule.mem_bot] using hx.1
  simp [hx0]

theorem zero_space_support {n : ℕ} : maxSupp (⊥:Submodule ℝ (E n))=∅ := by
  ext i
  simp [mem_support_iff_sigma_pos,zero_space_sigma]

theorem zero_space_condition {n : ℕ} : condMeasure (⊥:Submodule ℝ (E n))=1 := by
  simp [condMeasure,zero_space_support]

theorem full_space_sigma {n : ℕ} (i : Fin n) : sigmaI (⊤:Submodule ℝ (E n)) i=1 := by
  apply le_antisymm (sigma_bounds _ i).2
  apply le_csSup (image_bounded _ i)
  refine ⟨WithLp.toLp 2 (fun _=>1),⟨Submodule.mem_top,?_,?_⟩,rfl⟩ <;> simp [nonneg]

theorem full_space_support {n : ℕ} : maxSupp (⊤:Submodule ℝ (E n))=univ := by
  ext i
  simp [mem_support_iff_sigma_pos,full_space_sigma]

theorem empty_dimension_condition (L : Submodule ℝ (E 0)) : maxSupp L=∅ ∧ condMeasure L=1 := by
  have h : maxSupp L=∅:=eq_empty_iff_forall_notMem.mpr (fun i _=>Fin.elim0 i)
  exact ⟨h,by simp [condMeasure,h]⟩

theorem infinity_euclidean_distinction :
    supNorm (WithLp.toLp 2 (fun _:Fin 2=>(1:ℝ)))=1 ∧
      1 < ‖WithLp.toLp 2 (fun _:Fin 2=>(1:ℝ))‖ := by
  constructor
  · simp [supNorm]
  · have hs : ‖WithLp.toLp 2 (fun _:Fin 2=>(1:ℝ))‖^2=2 := by
      norm_num [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_two]
    have hn:=norm_nonneg (WithLp.toLp 2 (fun _:Fin 2=>(1:ℝ)))
    nlinarith

theorem zero_certificate_not_sufficient :
    (posL1 ((⊤:Submodule ℝ (E 1)).starProjection 0) ≤ supNorm (0:E 1)/2) ∧
      ¬(∀x∈(⊤:Submodule ℝ (E 1)),x∈nonneg 1 → x 0 ≤ supNorm x/2) := by
  constructor
  · simp [posL1,supNorm]
  · intro h
    have hh:=h (WithLp.toLp 2 (fun _=>1)) Submodule.mem_top (by simp [nonneg])
    norm_num [supNorm] at hh

theorem halted_has_no_step {n : ℕ} (L : Submodule ℝ (E n)) (σ : ℝ)
    (x : E n) (J : Finset (Fin n)) (r : ℕ) (s : A1State n) : ¬A1Step L σ (.halt x J r) s := by
  intro h
  cases h

theorem strict_trim_boundary :
    rescaleNext (1/2) (fun _:Fin 1=>1) univ 0 0 = .run (fun _=>2) univ 1 := by
  have he : Function.update (fun _:Fin 1=>(1:ℝ)) 0 2=(fun _=>2) := by
    funext i
    fin_cases i
    simp
  norm_num [rescaleNext,he]

theorem next_rescale_trims :
    rescaleNext (1/2) (fun _:Fin 1=>2) univ 1 0 = .halt 0 ∅ 2 := by
  have he : Function.update (fun _:Fin 1=>(2:ℝ)) 0 4=(fun _=>4) := by
    funext i
    fin_cases i
    simp
  norm_num [rescaleNext,he]
end Queelius.ProjectionRescaling.Controls

end

section
namespace ProjRescale.MaxSupport

open Classical in
/-- §2, p. 5: `J(L) = {i : σ_i(L) > 0}` and `σ(L) = min_{i ∈ J(L)} σ_i(L)`. -/
theorem sigma_i_observation {n : ℕ} (L : Submodule ℝ (E n)) :
    maxSupp L = Finset.univ.filter (fun i => 0 < sigmaI L i) ∧
      ∀ h : (maxSupp L).Nonempty, condMeasure L = (maxSupp L).inf' h (sigmaI L) := by
  exact Queelius.ProjectionRescaling.sigma_observation L

end ProjRescale.MaxSupport

namespace ProjRescale.MaxSupport

/-- Lemma 1, pp. 5–6. Let `P` be the orthogonal projection onto `L`, and let `z ∈ ℝⁿ₊ \ {0}` satisfy
`‖(Pz)⁺‖₁ ≤ ½‖z‖∞ = ½z_i`. Then every `x ∈ L ∩ ℝⁿ₊` has `x_i ≤ ‖x‖∞/2` (4), and for
`D = I + e_i e_iᵀ` the rescaled subspace satisfies `σ_i(DL) = 2σ_i(L)` and `σ_j(DL) = σ_j(L)` for
`j ≠ i`. -/
theorem lemma_1 {n : ℕ} (L : Submodule ℝ (E n)) (z : E n) (i : Fin n)
    (hz : z ∈ nonneg n) (hz0 : z ≠ 0) (hzi : supNorm z = z i)
    (hP : posL1 (L.starProjection z) ≤ supNorm z / 2) :
    (∀ x ∈ L, x ∈ nonneg n → x i ≤ supNorm x / 2) ∧
      sigmaI (diagScale (Function.update (fun _ => 1) i 2) L) i = 2 * sigmaI L i ∧
      ∀ j, j ≠ i → sigmaI (diagScale (Function.update (fun _ => 1) i 2) L) j = sigmaI L j := by
  exact Queelius.ProjectionRescaling.rescaling_lemma L z i hz hz0 hzi hP

end ProjRescale.MaxSupport

namespace ProjRescale.MaxSupport

/-- Corollary 1, p. 7. Let `σ > 0`. If `(x, J) = 𝒥(L, σ)` and `(x̂, Ĵ) = 𝒥(L⊥, σ)` satisfy
`J ∪ Ĵ = {1, …, n}`, then `J = J(L)`, `Ĵ = J(L⊥)`, and `x`, `x̂` are maximum support points of
`L ∩ ℝⁿ₊` and `L⊥ ∩ ℝⁿ₊`. -/
theorem corollary_1 {n : ℕ} (L : Submodule ℝ (E n)) (σ : ℝ) (hσ : 0 < σ)
    (x xh : E n) (J Jh : Finset (Fin n)) (r rh : ℕ)
    (hx : A1Halts L σ x J r) (hxh : A1Halts Lᗮ σ xh Jh rh) (hcov : J ∪ Jh = Finset.univ) :
    J = maxSupp L ∧ Jh = maxSupp Lᗮ ∧ IsMaxSupportPoint L x ∧ IsMaxSupportPoint Lᗮ xh := by
  exact Queelius.ProjectionRescaling.covering_halts_maximal L σ x xh J Jh r rh hx hxh hcov

end ProjRescale.MaxSupport

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

theorem simplex_max_positive (J : Finset (Fin n)) (z : E n) (hz : z∈simplexJ J)
    (i : Fin n) (hi : ∀j,z j≤z i) : 0<z i ∧ i∈J := by
  have hp : 0<z i := by
    by_contra h
    have hle:=le_of_not_gt h
    have hs : ∑j,z j≤0:=sum_nonpos (fun j _=>(hi j).trans hle)
    rw [hz.2.2] at hs
    norm_num at hs
  exact ⟨hp,by by_contra hn;have he:=hz.2.1 i hn;linarith⟩

def countInvariant (σ : ℝ) (N : ℕ) : A1State n → Prop
  | .run d J r => ∃k:Fin n→ℕ,r=∑j,k j ∧ (∀j,d j=(2:ℝ)^(k j)) ∧
      (∀j,k j≤N) ∧ ∀j∈J,d j≤1/σ
  | .halt _ _ r => r≤n*N

theorem sum_counts_bound (k : Fin n→ℕ) (N : ℕ) (hk : ∀j,k j≤N) :
    (∑j,k j)≤n*N := by
  calc
    _ ≤ ∑_j:Fin n,N := sum_le_sum (fun j _=>hk j)
    _ = n*N := by simp

theorem count_invariant_bound (σ : ℝ) (N : ℕ) (s : A1State n)
    (h : countInvariant σ N s) : s.rescalings≤n*N := by
  cases s with
  | halt x J r => exact h
  | run d J r => obtain ⟨k,rfl,_,hk,_⟩:=h;exact sum_counts_bound k N hk

theorem count_step (L : Submodule ℝ (E n)) (σ : ℝ) (N : ℕ)
    (hN : 1/σ<(2:ℝ)^N) {s t : A1State n} (h : A1Step L σ s t)
    (hs : countInvariant σ N s) : countInvariant σ N t := by
  cases h with
  | found d J r u hu hp => exact count_invariant_bound σ N (.run d J r) hs
  | rescale d J r z i hz hi hc =>
    obtain ⟨k,hr,hd,hk,hJ⟩:=hs
    have hiJ:= (simplex_max_positive J z hz i hi).2
    have hiN : k i<N := by
      by_contra hh
      have hle : N≤k i:=by omega
      have hp : (2:ℝ)^N≤(2:ℝ)^(k i):=pow_le_pow_right₀ (by norm_num) hle
      have hdi:=hJ i hiJ
      rw [hd i] at hdi
      linarith
    let k':Fin n→ℕ:=Function.update k i (k i+1)
    let d':Fin n→ℝ:=Function.update d i (2*d i)
    have hk' (j:Fin n) : k' j≤N := by
      by_cases hj:j=i
      · subst j;simp only [k',Function.update_self];omega
      · simpa only [k',Function.update_of_ne hj] using hk j
    have hd' (j:Fin n) : d' j=(2:ℝ)^(k' j) := by
      by_cases hj:j=i
      · subst j;simp [k',d',hd i,pow_succ,mul_comm]
      · simpa only [k',d',Function.update_of_ne hj] using hd j
    have hr' : r+1=∑j,k' j := by
      rw [hr]
      simp only [k']
      rw [sum_update_of_mem (mem_univ i)]
      simp only [sdiff_singleton_eq_erase]
      rw [←sum_erase_add _ _ (mem_univ i)]
      omega
    have hb : r+1≤n*N:=hr' ▸ sum_counts_bound k' N hk'
    have herase : ∀j∈J.erase i,d' j≤1/σ := by
      intro j hj
      have hjn: j≠i:=(mem_erase.mp hj).1
      simpa only [d',Function.update_of_ne hjn] using hJ j (mem_erase.mp hj).2
    have hkeep (ht : ¬1/σ<d' i) : ∀j∈J,d' j≤1/σ := by
      intro j hj
      by_cases hji:j=i
      · subst j;exact le_of_not_gt ht
      · simpa only [d',Function.update_of_ne hji] using hJ j hj
    change countInvariant σ N (if (if 1/σ<d' i then J.erase i else J)=∅
      then .halt 0 ∅ (r+1) else .run d' (if 1/σ<d' i then J.erase i else J) (r+1))
    split <;> split
    · exact hb
    · exact ⟨k',hr',hd',hk',herase⟩
    · exact hb
    · exact ⟨k',hr',hd',hk',hkeep (by assumption)⟩

theorem reachable_count_invariant (L : Submodule ℝ (E n)) (σ : ℝ) (hσ : σ≤1)
    (hσ0 : 0<σ) (N : ℕ) (hN : 1/σ<(2:ℝ)^N) (s : A1State n)
    (h : Relation.ReflTransGen (A1Step L σ) (A1Init n) s) : countInvariant σ N s := by
  induction h with
  | refl =>
    refine ⟨fun _=>0,by simp,by simp,by simp,?_⟩
    intro j hj
    exact (le_div_iff₀ hσ0).mpr (by simpa using hσ)
  | tail h hs ih => exact count_step L σ N hN hs ih

theorem floor_log_cap (σ : ℝ) (hσ0 : 0<σ) :
    1/σ<(2:ℝ)^(⌊Real.logb 2 (1/σ)⌋₊+1) := by
  rw [←Real.rpow_natCast]
  apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) (by positivity)).mp
  exact_mod_cast Nat.lt_floor_add_one (Real.logb 2 (1/σ))

theorem a1_count_bound (L : Submodule ℝ (E n)) (σ : ℝ) (hσ0 : 0<σ) (hσ1 : σ≤1)
    (s : A1State n) (h : Relation.ReflTransGen (A1Step L σ) (A1Init n) s) :
    s.rescalings≤n*(⌊Real.logb 2 (1/σ)⌋₊+1) :=
  count_invariant_bound σ _ s (reachable_count_invariant L σ hσ1 hσ0 _ (floor_log_cap σ hσ0) s h)
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling.Controls
open Finset Classical ProjRescale.MaxSupport

theorem zero_subspace_projection (d : Fin 1 → ℝ) (J : Finset (Fin 1)) (u : E 1) :
    projDLJ (⊥:Submodule ℝ (E 1)) d J u=0 := by
  simp [projDLJ,diagScale]

theorem zero_subspace_rescale (d : Fin 1 → ℝ) (r : ℕ) :
    A1Step (⊥:Submodule ℝ (E 1)) (1/2) (.run d univ r) (rescaleNext (1/2) d univ r 0) := by
  apply A1Step.rescale d univ r (WithLp.toLp 2 (fun _=>1)) 0
  · simp [simplexJ]
  · intro j
    rfl
  · simp [zero_subspace_projection,posL1,supNorm]

theorem zero_subspace_two_rescalings :
    A1Halts (⊥:Submodule ℝ (E 1)) (1/2) 0 ∅ 2 := by
  have h1:=zero_subspace_rescale (fun _=>1) 0
  rw [strict_trim_boundary] at h1
  have h2:=zero_subspace_rescale (fun _=>2) 1
  rw [next_rescale_trims] at h2
  exact (Relation.ReflTransGen.single h1).tail h2

theorem one_step_count_fails : ∃r,A1Halts (⊥:Submodule ℝ (E 1)) (1/2) 0 ∅ r ∧ 1 < r :=
  ⟨2,zero_subspace_two_rescalings,by norm_num⟩
end Queelius.ProjectionRescaling.Controls

end

section
namespace ProjRescale.MaxSupport
theorem partition_claim {n : ℕ} (L : Submodule ℝ (E n)) :
    maxSupp L ∩ maxSupp Lᗮ = ∅ ∧ maxSupp L ∪ maxSupp Lᗮ = Finset.univ :=
  Queelius.ProjectionRescaling.support_partition L
end ProjRescale.MaxSupport

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

theorem state_run_of_step (L : Submodule ℝ (E n)) (σ : ℝ) {s t : A1State n}
    (h : A1Step L σ s t) : s.IsRun := by cases h <;> trivial

theorem step_count_increases_when_running (L : Submodule ℝ (E n)) (σ : ℝ)
    {s t : A1State n} (h : A1Step L σ s t) (ht : t.IsRun) :
    t.rescalings=s.rescalings+1 := by
  cases h with
  | found d J r u hu hp => exact False.elim ht
  | rescale d J r z i hz hi hc =>
    unfold rescaleNext
    dsimp only
    split <;> split <;> rfl

theorem a1_no_infinite_execution (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ0 : 0<σ) (hσ1 : σ≤1) :
    ¬∃f:ℕ→A1State n,f 0=A1Init n ∧ ∀t,A1Step L σ (f t) (f (t+1)) := by
  rintro ⟨f,hf0,hf⟩
  have hreach (t:ℕ) : Relation.ReflTransGen (A1Step L σ) (A1Init n) (f t) := by
    induction t with
    | zero => rw [hf0]
    | succ t ih => exact ih.tail (hf t)
  have hc (t:ℕ) : (f t).rescalings=t := by
    induction t with
    | zero => simp [hf0,A1Init,A1State.rescalings]
    | succ t ih => rw [step_count_increases_when_running L σ (hf t) (state_run_of_step L σ (hf (t+1))),ih]
  let N:=n*(⌊Real.logb 2 (1/σ)⌋₊+1)
  have hb:=a1_count_bound L σ hσ0 hσ1 (f (N+1)) (hreach (N+1))
  rw [hc] at hb
  change N+1≤N at hb
  omega

/-- Four unconditional clauses of the corrected Proposition 1; its small-guess refinement remains separate. -/
theorem a1_unconditional_guarantees (hn : 0<n) (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ0 : 0<σ) (hσ1 : σ≤1) :
    (∀s,Relation.ReflTransGen (A1Step L σ) (A1Init n) s → s.IsRun → ∃s',A1Step L σ s s') ∧
    (¬∃f:ℕ→A1State n,f 0=A1Init n ∧ ∀t,A1Step L σ (f t) (f (t+1))) ∧
    (∀s,Relation.ReflTransGen (A1Step L σ) (A1Init n) s → s.rescalings≤n*(⌊Real.logb 2 (1/σ)⌋₊+1)) ∧
    (∀x J r,A1Halts L σ x J r → x∈L ∧ x∈nonneg n ∧ (∀j∈J,0<x j) ∧ J⊆maxSupp L) := by
  refine ⟨a1_never_stuck hn L σ,a1_no_infinite_execution L σ hσ0 hσ1,a1_count_bound L σ hσ0 hσ1,?_⟩
  intro x J r h
  have ho:=halting_output_good L σ x J r h
  exact ⟨ho.1,ho.2.1,fun j hj=>(ho.2.2 j).mpr hj,output_support_subset L x J ho⟩
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

theorem condition_le_sigma (L : Submodule ℝ (E n)) (i : Fin n) (hi : i∈maxSupp L) :
    condMeasure L ≤ sigmaI L i := by
  have h : (maxSupp L).Nonempty:=⟨i,hi⟩
  rw [condMeasure,dif_pos h]
  exact inf'_le _ hi

theorem simplex_max_sup (J : Finset (Fin n)) (z : E n) (hz : z∈simplexJ J)
    (i : Fin n) (hi : ∀j,z j ≤ z i) : supNorm z=z i := by
  letI : Nonempty (Fin n):=⟨i⟩
  apply le_antisymm
  · apply ciSup_le
    intro j
    simpa only [abs_of_nonneg (hz.1 j)] using hi j
  · exact nonneg_coordinate_le_sup z hz.1 i

theorem scaled_sigma_bound (L : Submodule ℝ (E n)) (d : Fin n→ℝ)
    (hd : ∀j,1 ≤ d j) (hf : ∀x∈box L,∀j,d j*x j ≤ 1) (i : Fin n) :
    d i*sigmaI L i ≤ 1 := by
  rw [←sigma_diagonal_transport L d hd hf i]
  exact (sigma_bounds _ i).2

theorem rescale_preserves_box (L : Submodule ℝ (E n)) (d : Fin n→ℝ)
    (J : Finset (Fin n)) (hd : ∀j,1 ≤ d j) (hJ : maxSupp L⊆J)
    (hf : ∀x∈box L,∀j,d j*x j ≤ 1) (z : E n) (i : Fin n)
    (hz : z∈simplexJ J) (hi : ∀j,z j ≤ z i)
    (hc : posL1 (projDLJ L d J z) ≤ supNorm z/2) :
    ∀x∈box L,∀j,Function.update d i (2*d i) j*x j ≤ 1 := by
  have hz0 : z≠0 := by
    intro he
    have hp:=(simplex_max_positive J z hz i hi).1
    simp [he] at hp
  let K:=diagScale d L⊓coordSub J
  have hhalf:=certificate_half_bound K z i hz.1 hz0 (simplex_max_sup J z hz i hi) hc
  intro x hx j
  by_cases hj:j=i
  · subst j
    let y:=Matrix.toEuclideanLin (Matrix.diagonal d) x
    have hyK : y∈K := by
      refine ⟨Submodule.mem_map.mpr ⟨x,hx.1,rfl⟩,?_⟩
      intro j hj
      have hjS : j∉maxSupp L:=fun h=>hj (hJ h)
      rw [show y j=d j*x j from diagonal_apply d x j]
      rw [outside_support_zero L x hx.1 hx.2.1 j hjS,mul_zero]
    have hyn : y∈nonneg n := by
      intro j
      rw [show y j=d j*x j from diagonal_apply d x j]
      exact mul_nonneg (by linarith [hd j]) (hx.2.1 j)
    have hybox : y∈box K:=⟨hyK,hyn,fun j=>by simpa only [y,diagonal_apply] using hf x hx j⟩
    have hh:=hhalf y hyK hyn
    have hs:=box_sup_le_one K y hybox i
    rw [show y i=d i*x i from diagonal_apply d x i] at hh
    simp only [Function.update_self]
    nlinarith
  · simpa only [Function.update_of_ne hj] using hf x hx j

theorem scaled_support_not_trimmed (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ : 0 < σ) (hsmall : σ ≤ condMeasure L) (d : Fin n→ℝ)
    (hd : ∀j,1 ≤ d j) (hf : ∀x∈box L,∀j,d j*x j ≤ 1)
    (i : Fin n) (ht : 1/σ < d i) : i∉maxSupp L := by
  intro hi
  have hsi:=hsmall.trans (condition_le_sigma L i hi)
  have hmul:=mul_le_mul_of_nonneg_left hsi (show 0 ≤ d i by linarith [hd i])
  have hb:=scaled_sigma_bound L d hd hf i
  have hh:=(div_lt_iff₀ hσ).mp ht
  nlinarith

theorem support_log_count (L : Submodule ℝ (E n)) (d : Fin n→ℝ)
    (hd : ∀j,1 ≤ d j) (hf : ∀x∈box L,∀j,d j*x j ≤ 1)
    (k : Fin n→ℕ) (hk : ∀j,d j=(2:ℝ)^(k j)) (i : Fin n) (hi : i∈maxSupp L) :
    k i ≤ ⌈Real.logb 2 (1/sigmaI L i)⌉₊ := by
  have hs : 0 < sigmaI L i:=(mem_support_iff_sigma_pos L i).mp hi
  have hp : (2:ℝ)^(k i) ≤ 1/sigmaI L i := by
    apply (le_div_iff₀ hs).mpr
    rw [←hk i]
    exact scaled_sigma_bound L d hd hf i
  have hl : (k i:ℝ) ≤ Real.logb 2 (1/sigmaI L i) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ) < 2) (by positivity)).mpr
    simpa only [Real.rpow_natCast] using hp
  exact_mod_cast hl.trans (Nat.le_ceil _)

def refinedCap (L : Submodule ℝ (E n)) (N : ℕ) (j : Fin n) : ℕ :=
  if j∈maxSupp L then ⌈Real.logb 2 (1/sigmaI L j)⌉₊ else N

theorem refined_sum_bound (L : Submodule ℝ (E n)) (N : ℕ) (d : Fin n→ℝ)
    (hd : ∀j,1 ≤ d j) (hf : ∀x∈box L,∀j,d j*x j ≤ 1)
    (k : Fin n→ℕ) (hk : ∀j,d j=(2:ℝ)^(k j)) (hN : ∀j,k j ≤ N) :
    (∑j,k j) ≤ ∑j,refinedCap L N j := by
  apply sum_le_sum
  intro j _
  by_cases hj:j∈maxSupp L
  · simpa only [refinedCap,if_pos hj] using support_log_count L d hd hf k hk j hj
  · simpa only [refinedCap,if_neg hj] using hN j

theorem refined_sum_formula (L : Submodule ℝ (E n)) (N : ℕ) :
    (∑j,refinedCap L N j)=
      (∑j∈maxSupp L,⌈Real.logb 2 (1/sigmaI L j)⌉₊)+(n-(maxSupp L).card)*N := by
  simp only [refinedCap,sum_ite]
  have h1 : univ.filter (fun j=>j∈maxSupp L)=maxSupp L:=by ext j;simp
  have h2 : univ.filter (fun j=>j∉maxSupp L)=univ\maxSupp L:=by ext j;simp
  rw [h1,h2]
  simp [card_sdiff_of_subset (subset_univ _)]
end Queelius.ProjectionRescaling

end

section
theorem Queelius.ProjectionRescaling.originalA1Progress : (
∀ (n : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀
      (L :
        @Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
          (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
            (@WithLp.instAddCommGroup
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  PiLp.innerProductSpace._proof_1))
              ((i : Fin n) → (fun (x : Fin n) => Real) i)
              (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)))
          (@WithLp.instModule
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
            (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
            (@Pi.Function.module (Fin n) Real Real Real.semiring
              (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
              (@Semiring.toModule Real Real.semiring))))
      (σ : Real),
      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) σ →
        @LT.lt Real Real.instLT σ (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
          ∀ (s : ProjRescale.MaxSupport.A1State n),
            @Relation.ReflTransGen (ProjRescale.MaxSupport.A1State n) (@ProjRescale.MaxSupport.A1Step n L σ)
                (ProjRescale.MaxSupport.A1Init n) s →
              @ProjRescale.MaxSupport.A1State.IsRun n s →
                @Exists (ProjRescale.MaxSupport.A1State n) fun (s' : ProjRescale.MaxSupport.A1State n) =>
                  @ProjRescale.MaxSupport.A1Step n L σ s s'
) := by
  intro n hn L σ hσ0 hσ1
  exact @Queelius.ProjectionRescaling.a1_never_stuck n hn L σ

theorem Queelius.ProjectionRescaling.originalA1Finite : (
∀ (n : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀
      (L :
        @Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
          (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
            (@WithLp.instAddCommGroup
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  PiLp.innerProductSpace._proof_1))
              ((i : Fin n) → (fun (x : Fin n) => Real) i)
              (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)))
          (@WithLp.instModule
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
            (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
            (@Pi.Function.module (Fin n) Real Real Real.semiring
              (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
              (@Semiring.toModule Real Real.semiring))))
      (σ : Real),
      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) σ →
        @LT.lt Real Real.instLT σ (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
          Not
            (@Exists (Nat → ProjRescale.MaxSupport.A1State n) fun (f : Nat → ProjRescale.MaxSupport.A1State n) =>
              And
                (@Eq (ProjRescale.MaxSupport.A1State n) (f (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (ProjRescale.MaxSupport.A1Init n))
                (∀ (t : Nat),
                  @ProjRescale.MaxSupport.A1Step n L σ (f t)
                    (f
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) t
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
) := by
  intro n hn L σ hσ0 hσ1
  exact @Queelius.ProjectionRescaling.a1_no_infinite_execution n L σ hσ0 hσ1.le

theorem Queelius.ProjectionRescaling.originalA1Count : (
∀ (n : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀
      (L :
        @Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
          (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
            (@WithLp.instAddCommGroup
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  PiLp.innerProductSpace._proof_1))
              ((i : Fin n) → (fun (x : Fin n) => Real) i)
              (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)))
          (@WithLp.instModule
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
            (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
            (@Pi.Function.module (Fin n) Real Real Real.semiring
              (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
              (@Semiring.toModule Real Real.semiring))))
      (σ : Real),
      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) σ →
        @LT.lt Real Real.instLT σ (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
          ∀ (s : ProjRescale.MaxSupport.A1State n),
            @Relation.ReflTransGen (ProjRescale.MaxSupport.A1State n) (@ProjRescale.MaxSupport.A1Step n L σ)
                (ProjRescale.MaxSupport.A1Init n) s →
              @LE.le Nat instLENat (@ProjRescale.MaxSupport.A1State.rescalings n s)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@Nat.floor Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (Real.logb
                        (@OfNat.ofNat Real (nat_lit 2)
                          (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) σ)))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
) := by
  intro n hn L σ hσ0 hσ1
  exact @Queelius.ProjectionRescaling.a1_count_bound n L σ hσ0 hσ1.le

theorem Queelius.ProjectionRescaling.originalA1Output : (
∀ (n : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀
      (L :
        @Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
          (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
            (@WithLp.instAddCommGroup
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  PiLp.innerProductSpace._proof_1))
              ((i : Fin n) → (fun (x : Fin n) => Real) i)
              (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)))
          (@WithLp.instModule
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
            (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
            (@Pi.Function.module (Fin n) Real Real Real.semiring
              (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
              (@Semiring.toModule Real Real.semiring))))
      (σ : Real),
      @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) σ →
        @LT.lt Real Real.instLT σ (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
          ∀ (x : ProjRescale.MaxSupport.E n) (J : Finset (Fin n)) (r : Nat),
            @ProjRescale.MaxSupport.A1Halts n L σ x J r →
              And
                (@Membership.mem (ProjRescale.MaxSupport.E n)
                  (@Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
                    (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                      (@WithLp.instAddCommGroup
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            PiLp.innerProductSpace._proof_1))
                        ((i : Fin n) → (fun (x : Fin n) => Real) i)
                        (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)))
                    (@WithLp.instModule
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          PiLp.innerProductSpace._proof_1))
                      Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                      (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
                      (@Pi.Function.module (Fin n) Real Real Real.semiring
                        (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                        (@Semiring.toModule Real Real.semiring))))
                  (@SetLike.instMembership
                    (@Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
                      (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                        (@WithLp.instAddCommGroup
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              PiLp.innerProductSpace._proof_1))
                          ((i : Fin n) → (fun (x : Fin n) => Real) i)
                          (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                            Real.instAddCommGroup)))
                      (@WithLp.instModule
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            PiLp.innerProductSpace._proof_1))
                        Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                        (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
                        (@Pi.Function.module (Fin n) Real Real Real.semiring
                          (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                          (@Semiring.toModule Real Real.semiring))))
                    (ProjRescale.MaxSupport.E n)
                    (@Submodule.setLike Real (ProjRescale.MaxSupport.E n) Real.semiring
                      (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                        (@WithLp.instAddCommGroup
                          (@OfNat.ofNat ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                              PiLp.innerProductSpace._proof_1))
                          ((i : Fin n) → (fun (x : Fin n) => Real) i)
                          (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                            Real.instAddCommGroup)))
                      (@WithLp.instModule
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            PiLp.innerProductSpace._proof_1))
                        Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                        (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
                        (@Pi.Function.module (Fin n) Real Real Real.semiring
                          (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                          (@Semiring.toModule Real Real.semiring)))))
                  L x)
                (And
                  (@Membership.mem (ProjRescale.MaxSupport.E n) (Set (ProjRescale.MaxSupport.E n))
                    (@Set.instMembership (ProjRescale.MaxSupport.E n)) (ProjRescale.MaxSupport.nonneg n) x)
                  (And
                    (∀ (j : Fin n),
                      @Membership.mem (Fin n) (Finset (Fin n))
                          (@SetLike.instMembership (Finset (Fin n)) (Fin n) (@Finset.instSetLike (Fin n))) J j →
                        @LT.lt ((fun (x : Fin n) => Real) j) Real.instLT
                          (@OfNat.ofNat ((fun (x : Fin n) => Real) j) (nat_lit 0)
                            (@Zero.toOfNat0 ((fun (x : Fin n) => Real) j) Real.instZero))
                          (@WithLp.ofLp
                            (@OfNat.ofNat ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                PiLp.innerProductSpace._proof_1))
                            ((i : Fin n) → (fun (x : Fin n) => Real) i) x j))
                    (@LE.le (Finset (Fin n))
                      (@Preorder.toLE (Finset (Fin n))
                        (@PartialOrder.toPreorder (Finset (Fin n)) (@Finset.instPartialOrder (Fin n))))
                      J (@ProjRescale.MaxSupport.maxSupp n L))))
) := by
  intro n hn L σ hσ0 hσ1
  exact (Queelius.ProjectionRescaling.a1_unconditional_guarantees hn L σ hσ0 hσ1.le).2.2.2

end

section
noncomputable section
namespace Queelius.ProjectionRescaling.Controls
open Finset Classical ProjRescale.MaxSupport

theorem coordinate_support {n:ℕ} (J : Finset (Fin n)) : maxSupp (coordSub J)=J := by
  ext j
  constructor
  · intro hj
    obtain ⟨x,hx,hxn,hxj⟩:=(mem_filter.mp hj).2
    by_contra hn
    have h:=hx j hn
    linarith
  · intro hj
    refine mem_filter.mpr ⟨mem_univ _,EuclideanSpace.single j (1:ℝ),single_in_coord J j hj,?_,?_⟩
    · exact (single_in_simplex J j hj).1
    · simp

theorem coordinate_orthogonal_support {n:ℕ} (J : Finset (Fin n)) :
    maxSupp (coordSub J)ᗮ=Jᶜ := by
  have hd:=support_disjoint (coordSub J)
  have hc:= (support_partition (coordSub J)).2
  rw [coordinate_support] at hd hc
  ext j
  constructor
  · intro hj
    exact mem_compl.mpr (fun h=>disjoint_left.mp hd h hj)
  · intro hj
    have hh : j∈J∪maxSupp (coordSub J)ᗮ:=by rw [hc];exact mem_univ _
    exact (mem_union.mp hh).resolve_left (mem_compl.mp hj)

theorem empty_simplex {n:ℕ} (x:E n) : x∉simplexJ ∅ := by
  intro h
  have hz : x=0 := by ext j;exact h.2.1 j (notMem_empty _)
  have hs:=h.2.2
  simp [hz] at hs

theorem empty_run_stuck {n:ℕ} (L : Submodule ℝ (E n)) (σ:ℝ)
    (d:Fin n→ℝ) (r:ℕ) (s:A1State n) : ¬A1Step L σ (.run d ∅ r) s := by
  intro h
  cases h with
  | found d J r u hu hp => exact empty_simplex u hu
  | rescale d J r z i hz hi hc => exact empty_simplex z hz

theorem zero_dimension_initial_stuck (L : Submodule ℝ (E 0)) (σ:ℝ) :
    ¬∃s,A1Step L σ (A1Init 0) s := by
  rintro ⟨s,h⟩
  have he : (univ:Finset (Fin 0))=∅:=by ext i;exact Fin.elim0 i
  change A1Step L σ (.run (fun _=>1) univ 0) s at h
  rw [he] at h
  exact empty_run_stuck L σ _ _ _ h

theorem threshold_one_zero_halts : A1Halts (⊥:Submodule ℝ (E 1)) 1 0 ∅ 1 := by
  have h : A1Step (⊥:Submodule ℝ (E 1)) 1 (.run (fun _=>1) univ 0)
      (rescaleNext 1 (fun _=>1) univ 0 0) := by
    apply A1Step.rescale _ _ _ (WithLp.toLp 2 (fun _=>1)) 0
    · simp [simplexJ]
    · intro j;rfl
    · simp [zero_subspace_projection,posL1,supNorm]
  have he : Function.update (fun _:Fin 1=>(1:ℝ)) 0 2=(fun _=>2) := by
    funext i;fin_cases i;simp
  have hh : rescaleNext 1 (fun _:Fin 1=>1) univ 0 0 = .halt 0 ∅ 1 := by
    norm_num [rescaleNext,he]
  rw [hh] at h
  exact Relation.ReflTransGen.single h
end Queelius.ProjectionRescaling.Controls

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

def smallGuessInvariant (L : Submodule ℝ (E n)) (N : ℕ) : A1State n→Prop
  | .run d J _ => (∀j,1 ≤ d j) ∧ maxSupp L⊆J ∧ ∀x∈box L,∀j,d j*x j ≤ 1
  | .halt _ J r => J=maxSupp L ∧ r ≤ ∑j,refinedCap L N j

theorem small_guess_step (L : Submodule ℝ (E n)) (σ : ℝ) (hσ : 0 < σ)
    (hsmall : σ ≤ condMeasure L) (N : ℕ) (hN : 1/σ < (2:ℝ)^N)
    {s t : A1State n} (h : A1Step L σ s t) (hs : smallGuessInvariant L N s)
    (hcount : countInvariant σ N s) : smallGuessInvariant L N t := by
  cases h with
  | found d J r u hu hp =>
    obtain ⟨hd,hJ,hf⟩:=hs
    obtain ⟨k,hr,hdk,hk,_⟩:=hcount
    have ho:=found_output L d (fun j=>lt_of_lt_of_le (by norm_num) (hd j)) J u hp
    refine ⟨(output_support_subset L _ J ho).antisymm hJ,?_⟩
    rw [hr]
    exact refined_sum_bound L N d hd hf k hdk hk
  | rescale d J r z i hz hi hc =>
    obtain ⟨hd,hJ,hf⟩:=hs
    obtain ⟨k,hr,hdk,hk,hcur⟩:=hcount
    let k':Fin n→ℕ:=Function.update k i (k i+1)
    let d':Fin n→ℝ:=Function.update d i (2*d i)
    let J':Finset (Fin n):=if 1/σ < d' i then J.erase i else J
    have hd' : ∀j,1 ≤ d' j := by
      intro j
      by_cases hj:j=i
      · subst j;simp only [d',Function.update_self];linarith [hd i]
      · simpa only [d',Function.update_of_ne hj] using hd j
    have hf' : ∀x∈box L,∀j,d' j*x j ≤ 1:=rescale_preserves_box L d J hd hJ hf z i hz hi hc
    have hcover : maxSupp L⊆J' := by
      dsimp [J']
      split
      next ht =>
        have hnot:=scaled_support_not_trimmed L σ hσ hsmall d' hd' hf' i ht
        intro j hj
        exact mem_erase.mpr ⟨fun he=>hnot (he ▸ hj),hJ hj⟩
      next ht => exact hJ
    have hiJ:= (simplex_max_positive J z hz i hi).2
    have hiN : k i < N := by
      by_contra hh
      have hle : N ≤ k i:=by omega
      have hp : (2:ℝ)^N ≤ (2:ℝ)^(k i):=pow_le_pow_right₀ (by norm_num) hle
      have hdi:=hcur i hiJ
      rw [hdk i] at hdi
      linarith
    have hk' (j:Fin n) : k' j ≤ N := by
      by_cases hj:j=i
      · subst j;simp only [k',Function.update_self];omega
      · simpa only [k',Function.update_of_ne hj] using hk j
    have hdk' (j:Fin n) : d' j=(2:ℝ)^(k' j) := by
      by_cases hj:j=i
      · subst j;simp [k',d',hdk i,pow_succ,mul_comm]
      · simpa only [k',d',Function.update_of_ne hj] using hdk j
    have hr' : r+1=∑j,k' j := by
      rw [hr]
      simp only [k']
      rw [sum_update_of_mem (mem_univ i)]
      simp only [sdiff_singleton_eq_erase]
      rw [←sum_erase_add _ _ (mem_univ i)]
      omega
    have hb : r+1 ≤ ∑j,refinedCap L N j := by
      rw [hr']
      exact refined_sum_bound L N d' hd' hf' k' hdk' hk'
    change smallGuessInvariant L N (if J'=∅ then .halt 0 ∅ (r+1) else .run d' J' (r+1))
    by_cases he:J'=∅
    · rw [if_pos he]
      exact ⟨(subset_empty.mp (he ▸ hcover)).symm,hb⟩
    · rw [if_neg he]
      exact ⟨hd',hcover,hf'⟩

theorem reachable_small_guess (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hsmall : σ ≤ condMeasure L)
    (N : ℕ) (hN : 1/σ < (2:ℝ)^N) (s : A1State n)
    (h : Relation.ReflTransGen (A1Step L σ) (A1Init n) s) : smallGuessInvariant L N s := by
  induction h with
  | refl =>
    refine ⟨fun _=>le_rfl,subset_univ _,?_⟩
    intro x hx j
    simpa only [one_mul] using hx.2.2 j
  | tail h hs ih =>
    exact small_guess_step L σ hσ0 hsmall N hN hs ih
      (reachable_count_invariant L σ hσ1 hσ0 N hN _ h)

theorem small_guess_halts (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hsmall : σ ≤ condMeasure L)
    (x : E n) (J : Finset (Fin n)) (r : ℕ) (h : A1Halts L σ x J r) :
    J=maxSupp L ∧ r ≤ (∑j∈maxSupp L,⌈Real.logb 2 (1/sigmaI L j)⌉₊)+
      (n-(maxSupp L).card)*(⌊Real.logb 2 (1/σ)⌋₊+1) := by
  have hi:=reachable_small_guess L σ hσ0 hσ1 hsmall _ (floor_log_cap σ hσ0) (.halt x J r) h
  change J=maxSupp L ∧ r ≤ ∑j,refinedCap L (⌊Real.logb 2 (1/σ)⌋₊+1) j at hi
  rwa [refined_sum_formula] at hi

theorem proposition_one_complete (hn : 0 < n) (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∀s,Relation.ReflTransGen (A1Step L σ) (A1Init n) s → s.IsRun → ∃s',A1Step L σ s s') ∧
    (¬∃f:ℕ→A1State n,f 0=A1Init n ∧ ∀t,A1Step L σ (f t) (f (t+1))) ∧
    (∀s,Relation.ReflTransGen (A1Step L σ) (A1Init n) s → s.rescalings ≤ n*(⌊Real.logb 2 (1/σ)⌋₊+1)) ∧
    (∀x J r,A1Halts L σ x J r → x∈L ∧ x∈nonneg n ∧ (∀j∈J,0 < x j) ∧ J⊆maxSupp L) ∧
    (σ ≤ condMeasure L → ∀x J r,A1Halts L σ x J r → J=maxSupp L ∧
      r ≤ (∑j∈maxSupp L,⌈Real.logb 2 (1/sigmaI L j)⌉₊)+(n-(maxSupp L).card)*(⌊Real.logb 2 (1/σ)⌋₊+1)) := by
  have h:=a1_unconditional_guarantees hn L σ hσ0 hσ1.le
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,fun hsmall=>small_guess_halts L σ hσ0 hσ1.le hsmall⟩
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling.Controls
open Finset Classical ProjRescale.MaxSupport

theorem full_space_condition {n : ℕ} : condMeasure (⊤:Submodule ℝ (E n))=1 := by
  apply le_antisymm (condition_bounds _).2
  unfold condMeasure
  split
  next h => exact le_inf' h _ (fun i hi=>by rw [full_space_sigma])
  next h => rfl

theorem full_space_halts_without_rescaling {n : ℕ} (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (x:E n) (J:Finset (Fin n)) (r:ℕ)
    (h:A1Halts (⊤:Submodule ℝ (E n)) σ x J r) : J=univ ∧ r=0 := by
  have hh:=small_guess_halts (⊤:Submodule ℝ (E n)) σ hσ0 hσ1
    (by simpa only [full_space_condition] using hσ1) x J r h
  simpa [full_space_support,full_space_sigma] using hh
end Queelius.ProjectionRescaling.Controls

end

section
namespace ProjRescale.MaxSupport

/-- Proposition 1, p. 6, corrected. For `σ ∈ (0, 1)`, every execution of Algorithm 1 on `(L, σ)`
can always continue until it halts, no execution is infinite, every execution performs at most
`n(⌊log₂(1/σ)⌋ + 1)` rescaling steps, and on halting it outputs `x ∈ L ∩ ℝⁿ₊` with `x_J > 0` for
some `J ⊆ J(L)`. If moreover `σ ≤ σ(L)`, then `J = J(L)` and the number of rescaling steps is at most
`∑_{i ∈ J(L)} ⌈log₂(1/σ_i(L))⌉ + (n − |J(L)|)(⌊log₂(1/σ)⌋ + 1)`. -/
theorem proposition_1 (n : ℕ) (hn : 0 < n) (L : Submodule ℝ (E n)) (σ : ℝ)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (∀ s, Relation.ReflTransGen (A1Step L σ) (A1Init n) s → s.IsRun →
        ∃ s', A1Step L σ s s') ∧
      (¬ ∃ f : ℕ → A1State n, f 0 = A1Init n ∧ ∀ t, A1Step L σ (f t) (f (t + 1))) ∧
      (∀ s, Relation.ReflTransGen (A1Step L σ) (A1Init n) s →
        s.rescalings ≤ n * (⌊Real.logb 2 (1 / σ)⌋₊ + 1)) ∧
      (∀ x J r, A1Halts L σ x J r →
        x ∈ L ∧ x ∈ nonneg n ∧ (∀ j ∈ J, 0 < x j) ∧ J ⊆ maxSupp L) ∧
      (σ ≤ condMeasure L → ∀ x J r, A1Halts L σ x J r →
        J = maxSupp L ∧
          r ≤ ∑ j ∈ maxSupp L, ⌈Real.logb 2 (1 / sigmaI L j)⌉₊ +
            (n - (maxSupp L).card) * (⌊Real.logb 2 (1 / σ)⌋₊ + 1)) := by
  exact Queelius.ProjectionRescaling.proposition_one_complete hn L σ hσ0 hσ1

end ProjRescale.MaxSupport

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

def a2Trace (L : Submodule ℝ (E n)) : A2State n → Prop
  | .callL _ σ _ s => 0 < σ ∧ σ < 1 ∧ Relation.ReflTransGen (A1Step L σ) (A1Init n) s
  | .callLperp _ σ _ x J s => 0 < σ ∧ σ < 1 ∧ (∃r,A1Halts L σ x J r) ∧
      Relation.ReflTransGen (A1Step Lᗮ σ) (A1Init n) s
  | .done _ _ x J xh Jh =>
      (J=maxSupp L ∧ x∈L ∧ x∈nonneg n ∧ ∀j∈J,0 < x j) ∧
      (Jh=maxSupp Lᗮ ∧ xh∈Lᗮ ∧ xh∈nonneg n ∧ ∀j∈Jh,0 < xh j)

theorem a2_trace_step (L : Submodule ℝ (E n)) {s t : A2State n}
    (h : A2Step L s t) (hs : a2Trace L s) : a2Trace L t := by
  cases h with
  | stepL i σ R s s' h => exact ⟨hs.1,hs.2.1,hs.2.2.tail h⟩
  | retL i σ R x J r => exact ⟨hs.1,hs.2.1,⟨r,hs.2.2⟩,Relation.ReflTransGen.refl⟩
  | stepLperp i σ R x J s s' h => exact ⟨hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.tail h⟩
  | halt i σ R x J xh Jh r hcov =>
    obtain ⟨rL,hL⟩:=hs.2.2.1
    have ho:=covering_halts_maximal L σ x xh J Jh rL r hL hs.2.2.2 hcov
    exact ⟨⟨ho.1,ho.2.2.1.1,ho.2.2.1.2.1,fun j hj=>(ho.2.2.1.2.2 j).mpr (ho.1 ▸ hj)⟩,
      ⟨ho.2.1,ho.2.2.2.1,ho.2.2.2.2.1,fun j hj=>(ho.2.2.2.2.2 j).mpr (ho.2.1 ▸ hj)⟩⟩
  | next i σ R x J xh Jh r hcov =>
    exact ⟨sq_pos_of_pos hs.1,pow_lt_one₀ hs.1.le hs.2.1 (by norm_num),Relation.ReflTransGen.refl⟩

theorem a2_reachable_trace (L : Submodule ℝ (E n)) (s : A2State n)
    (h : Relation.ReflTransGen (A2Step L) (A2Init n) s) : a2Trace L s := by
  induction h with
  | refl => exact ⟨by norm_num,by norm_num,Relation.ReflTransGen.refl⟩
  | tail h hs ih => exact a2_trace_step L hs ih

theorem a2_never_stuck (hn : 0 < n) (L : Submodule ℝ (E n)) (s : A2State n)
    (h : Relation.ReflTransGen (A2Step L) (A2Init n) s) (hr : ¬s.IsDone) :
    ∃s',A2Step L s s' := by
  have ht:=a2_reachable_trace L s h
  cases s with
  | callL i σ R a =>
    cases a with
    | run d J r =>
      obtain ⟨t,hstep⟩:=a1_never_stuck hn L σ (.run d J r) ht.2.2 trivial
      exact ⟨_,A2Step.stepL i σ R _ t hstep⟩
    | halt x J r => exact ⟨_,A2Step.retL i σ R x J r⟩
  | callLperp i σ R x J a =>
    cases a with
    | run d Jh r =>
      obtain ⟨t,hstep⟩:=a1_never_stuck hn Lᗮ σ (.run d Jh r) ht.2.2.2 trivial
      exact ⟨_,A2Step.stepLperp i σ R x J _ t hstep⟩
    | halt xh Jh r =>
      by_cases hcov:J∪Jh=univ
      · exact ⟨_,A2Step.halt i σ R x J xh Jh r hcov⟩
      · exact ⟨_,A2Step.next i σ R x J xh Jh r hcov⟩
  | done => exact False.elim (hr trivial)

theorem a2_output_correct (L : Submodule ℝ (E n)) (i R : ℕ) (x : E n) (J : Finset (Fin n))
    (xh : E n) (Jh : Finset (Fin n))
    (h : Relation.ReflTransGen (A2Step L) (A2Init n) (.done i R x J xh Jh)) :
    (J=maxSupp L ∧ x∈L ∧ x∈nonneg n ∧ ∀j∈J,0 < x j) ∧
      (Jh=maxSupp Lᗮ ∧ xh∈Lᗮ ∧ xh∈nonneg n ∧ ∀j∈Jh,0 < xh j) :=
  a2_reachable_trace L _ h
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

theorem a1_schedule_count (L : Submodule ℝ (E n)) (i : ℕ) (σ : ℝ)
    (hσ : σ=outerGuess i) (s : A1State n)
    (h : Relation.ReflTransGen (A1Step L σ) (A1Init n) s) : s.rescalings ≤ outerCap n i := by
  subst σ
  have hb:=a1_count_bound L (outerGuess i) (outer_guess_pos i) (outer_guess_lt_one i).le s h
  rwa [outer_guess_log] at hb

def a2Counters (K : ℕ) : A2State n → Prop
  | .callL i σ R _ => 1 ≤ i ∧ i ≤ K ∧ σ=outerGuess i ∧ R ≤ outerSpent n (i-1)
  | .callLperp i σ R _ _ _ => 1 ≤ i ∧ i ≤ K ∧ σ=outerGuess i ∧
      R ≤ outerSpent n (i-1)+outerCap n i
  | .done i R _ _ _ _ => 1 ≤ i ∧ i ≤ K ∧ R ≤ outerSpent n i

theorem a2_counters_step (L : Submodule ℝ (E n)) (K : ℕ)
    (hsmall : outerGuess K ≤ min (condMeasure L) (condMeasure Lᗮ))
    {s t : A2State n} (h : A2Step L s t) (ht : a2Trace L s) (hs : a2Counters K s) :
    a2Counters K t := by
  cases h with
  | stepL => exact hs
  | retL i σ R x J r =>
    have hb:=a1_schedule_count L i σ hs.2.2.1 (.halt x J r) ht.2.2
    change r ≤ outerCap n i at hb
    exact ⟨hs.1,hs.2.1,hs.2.2.1,Nat.add_le_add hs.2.2.2 hb⟩
  | stepLperp => exact hs
  | halt i σ R x J xh Jh r hcov =>
    have hR:=hs.2.2.2
    have hb:=a1_schedule_count Lᗮ i σ hs.2.2.1 (.halt xh Jh r) ht.2.2.2
    change r ≤ outerCap n i at hb
    have he:=outer_spent_step n i hs.1
    refine ⟨hs.1,hs.2.1,?_⟩
    omega
  | next i σ R x J xh Jh r hcov =>
    have hR:=hs.2.2.2
    have hiK:=hs.2.1
    have hi : i < K := by
      by_contra hh
      have he : i=K := by omega
      subst i
      obtain ⟨rL,hL⟩:=ht.2.2.1
      have hlow : σ ≤ min (condMeasure L) (condMeasure Lᗮ) := hs.2.2.1 ▸ hsmall
      have hJ:=(small_guess_halts L σ ht.1 ht.2.1.le (hlow.trans (min_le_left _ _)) x J rL hL).1
      have hJh:=(small_guess_halts Lᗮ σ ht.1 ht.2.1.le (hlow.trans (min_le_right _ _)) xh Jh r ht.2.2.2).1
      apply hcov
      rw [hJ,hJh]
      exact (support_partition L).2
    have hb:=a1_schedule_count Lᗮ i σ hs.2.2.1 (.halt xh Jh r) ht.2.2.2
    change r ≤ outerCap n i at hb
    have he:=outer_spent_step n i hs.1
    refine ⟨by omega,by omega,?_,?_⟩
    · rw [hs.2.2.1,outer_guess_next i hs.1]
    · simp only [Nat.add_sub_cancel]
      omega

theorem a2_reachable_counters (L : Submodule ℝ (E n)) (K : ℕ) (hK : 1 ≤ K)
    (hsmall : outerGuess K ≤ min (condMeasure L) (condMeasure Lᗮ))
    (s : A2State n) (h : Relation.ReflTransGen (A2Step L) (A2Init n) s) : a2Counters K s := by
  induction h with
  | refl => exact ⟨le_rfl,hK,outer_guess_one.symm,by simp [outerSpent]⟩
  | tail h hs ih => exact a2_counters_step L K hsmall hs (a2_reachable_trace L _ h) ih

theorem a2_generic_bounds (L : Submodule ℝ (E n)) (K : ℕ) (hK : 1 ≤ K)
    (hsmall : outerGuess K ≤ min (condMeasure L) (condMeasure Lᗮ))
    (s : A2State n) (h : Relation.ReflTransGen (A2Step L) (A2Init n) s) :
    s.iter ≤ K ∧ s.rescalings ≤ outerSpent n K := by
  have ht:=a2_reachable_trace L s h
  have hc:=a2_reachable_counters L K hK hsmall s h
  cases s with
  | callL i σ R a =>
    have hR:=hc.2.2.2
    have hb:=a1_schedule_count L i σ hc.2.2.1 a ht.2.2
    have he:=outer_spent_step n i hc.1
    have hm:=outer_spent_mono n hc.2.1
    exact ⟨hc.2.1,by change R+a.rescalings ≤ outerSpent n K;omega⟩
  | callLperp i σ R x J a =>
    have hR:=hc.2.2.2
    have hb:=a1_schedule_count Lᗮ i σ hc.2.2.1 a ht.2.2.2
    have he:=outer_spent_step n i hc.1
    have hm:=outer_spent_mono n hc.2.1
    exact ⟨hc.2.1,by change R+a.rescalings ≤ outerSpent n K;omega⟩
  | done i R x J xh Jh => exact ⟨hc.2.1,hc.2.2.trans (outer_spent_mono n hc.2.1)⟩

theorem a2_exact_bounds (L : Submodule ℝ (E n)) (s : A2State n)
    (h : Relation.ReflTransGen (A2Step L) (A2Init n) s) :
    s.iter ≤ kIter (min (condMeasure L) (condMeasure Lᗮ)) ∧
      s.rescalings ≤ 2*n*(2^kIter (min (condMeasure L) (condMeasure Lᗮ))-1+
        kIter (min (condMeasure L) (condMeasure Lᗮ))) := by
  have hm : 0 < min (condMeasure L) (condMeasure Lᗮ) :=
    lt_min (condition_bounds L).1 (condition_bounds Lᗮ).1
  have hm1 : min (condMeasure L) (condMeasure Lᗮ) ≤ 1 := (min_le_left _ _).trans (condition_bounds L).2
  have hb:=a2_generic_bounds L _ (le_max_left _ _) (outer_guess_at_k _ hm hm1) s h
  rwa [outer_spent_closed] at hb
end Queelius.ProjectionRescaling

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport
variable {n : ℕ}

def a1Phase : A1State n → ℕ
  | .run _ _ _ => 0
  | .halt _ _ _ => 1
def a2Phase : A2State n → ℕ
  | .callL _ _ _ s => a1Phase s
  | .callLperp _ _ _ _ _ s => 2+a1Phase s
  | .done _ _ _ _ _ _ => 4
def a2Ticks (s : A2State n) : ℕ := 2*s.rescalings+4*s.iter+a2Phase s

theorem a1_step_phase_increases (L : Submodule ℝ (E n)) (σ : ℝ) {s t : A1State n}
    (h : A1Step L σ s t) : 2*s.rescalings+a1Phase s < 2*t.rescalings+a1Phase t := by
  cases h with
  | found => simp [a1Phase,A1State.rescalings]
  | rescale =>
    unfold rescaleNext
    dsimp only
    split <;> split <;> simp [a1Phase,A1State.rescalings] <;> omega

theorem a2_step_ticks_increases (L : Submodule ℝ (E n)) {s t : A2State n}
    (h : A2Step L s t) : a2Ticks s < a2Ticks t := by
  cases h with
  | stepL i σ R s t h =>
    have hp:=a1_step_phase_increases L σ h
    simp only [a2Ticks,A2State.rescalings,A2State.iter,a2Phase]
    omega
  | retL => simp [a2Ticks,A2State.rescalings,A2State.iter,a2Phase,a1Phase,A1Init,A1State.rescalings] <;> omega
  | stepLperp i σ R x J s t h =>
    have hp:=a1_step_phase_increases Lᗮ σ h
    simp only [a2Ticks,A2State.rescalings,A2State.iter,a2Phase]
    omega
  | halt => simp [a2Ticks,A2State.rescalings,A2State.iter,a2Phase,a1Phase,A1State.rescalings] <;> omega
  | next => simp [a2Ticks,A2State.rescalings,A2State.iter,a2Phase,a1Phase,A1Init,A1State.rescalings] <;> omega

theorem a2_phase_bound (s : A2State n) : a2Phase s ≤ 4 := by
  cases s with
  | callL i σ R a => cases a <;> norm_num [a2Phase,a1Phase]
  | callLperp i σ R x J a => cases a <;> norm_num [a2Phase,a1Phase]
  | done => rfl

theorem a2_no_infinite_execution (L : Submodule ℝ (E n)) :
    ¬∃f:ℕ→A2State n,f 0=A2Init n ∧ ∀t,A2Step L (f t) (f (t+1)) := by
  rintro ⟨f,hf0,hf⟩
  have hreach (t : ℕ) : Relation.ReflTransGen (A2Step L) (A2Init n) (f t) := by
    induction t with
    | zero => rw [hf0]
    | succ t ih => exact ih.tail (hf t)
  have ht (t : ℕ) : t ≤ a2Ticks (f t) := by
    induction t with
    | zero => omega
    | succ t ih => have hp:=a2_step_ticks_increases L (hf t);omega
  let K:=kIter (min (condMeasure L) (condMeasure Lᗮ))
  let B:=2*n*(2^K-1+K)
  let N:=2*B+4*K+4
  have hb:=a2_exact_bounds L (f (N+1)) (hreach (N+1))
  have hp:=a2_phase_bound (f (N+1))
  have ht':=ht (N+1)
  change (f (N+1)).iter ≤ K ∧ (f (N+1)).rescalings ≤ B at hb
  dsimp [a2Ticks] at ht'
  dsimp [N] at ht' hb hp
  omega

theorem outer_root (hn : 0 < n) (L : Submodule ℝ (E n)) :
    (∀s,Relation.ReflTransGen (A2Step L) (A2Init n) s → ¬s.IsDone → ∃s',A2Step L s s') ∧
    (¬∃f:ℕ→A2State n,f 0=A2Init n ∧ ∀t,A2Step L (f t) (f (t+1))) ∧
    (∀s,Relation.ReflTransGen (A2Step L) (A2Init n) s →
      s.iter ≤ kIter (min (condMeasure L) (condMeasure Lᗮ))) ∧
    (∀s,Relation.ReflTransGen (A2Step L) (A2Init n) s →
      s.rescalings ≤ 2*n*(2^kIter (min (condMeasure L) (condMeasure Lᗮ))-1+
        kIter (min (condMeasure L) (condMeasure Lᗮ)))) ∧
    (∀i R x J xh Jh,Relation.ReflTransGen (A2Step L) (A2Init n) (.done i R x J xh Jh) →
      (J=maxSupp L ∧ x∈L ∧ x∈nonneg n ∧ ∀j∈J,0 < x j) ∧
      (Jh=maxSupp Lᗮ ∧ xh∈Lᗮ ∧ xh∈nonneg n ∧ ∀j∈Jh,0 < xh j)) := by
  exact ⟨a2_never_stuck hn L,a2_no_infinite_execution L,
    fun s hs=>(a2_exact_bounds L s hs).1,fun s hs=>(a2_exact_bounds L s hs).2,a2_output_correct L⟩
end Queelius.ProjectionRescaling

end

section
theorem submission_primary_solution : (
  ∀ (n : Nat),
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
      ∀
        (L :
          @Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
            (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
              (@WithLp.instAddCommGroup
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    PiLp.innerProductSpace._proof_1))
                ((i : Fin n) → (fun (x : Fin n) => Real) i)
                (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)))
            (@WithLp.instModule
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  PiLp.innerProductSpace._proof_1))
              Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
              (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
              (@Pi.Function.module (Fin n) Real Real Real.semiring
                (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                (@Semiring.toModule Real Real.semiring)))),
        And
          (∀ (s : ProjRescale.MaxSupport.A2State n),
            @Relation.ReflTransGen (ProjRescale.MaxSupport.A2State n) (@ProjRescale.MaxSupport.A2Step n L)
                (ProjRescale.MaxSupport.A2Init n) s →
              Not (@ProjRescale.MaxSupport.A2State.IsDone n s) →
                @Exists (ProjRescale.MaxSupport.A2State n) fun (s' : ProjRescale.MaxSupport.A2State n) =>
                  @ProjRescale.MaxSupport.A2Step n L s s')
          (And
            (Not
              (@Exists (Nat → ProjRescale.MaxSupport.A2State n) fun (f : Nat → ProjRescale.MaxSupport.A2State n) =>
                And
                  (@Eq (ProjRescale.MaxSupport.A2State n) (f (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (ProjRescale.MaxSupport.A2Init n))
                  (∀ (t : Nat),
                    @ProjRescale.MaxSupport.A2Step n L (f t)
                      (f
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) t
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
            (And
              (∀ (s : ProjRescale.MaxSupport.A2State n),
                @Relation.ReflTransGen (ProjRescale.MaxSupport.A2State n) (@ProjRescale.MaxSupport.A2Step n L)
                    (ProjRescale.MaxSupport.A2Init n) s →
                  @LE.le Nat instLENat (@ProjRescale.MaxSupport.A2State.iter n s)
                    (ProjRescale.MaxSupport.kIter
                      (@Min.min Real Real.instMin (@ProjRescale.MaxSupport.condMeasure n L)
                        (@ProjRescale.MaxSupport.condMeasure n
                          (@Submodule.orthogonal Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                            (@PiLp.normedAddCommGroup
                              (@OfNat.ofNat ENNReal (nat_lit 2)
                                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                  (@AddMonoidWithOne.toNatCast ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                  PiLp.innerProductSpace._proof_1))
                              (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n) fun (i : Fin n) =>
                              Real.normedAddCommGroup)
                            (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                              (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup) fun (i : Fin n) =>
                              @RCLike.toInnerProductSpaceReal Real Real.instRCLike)
                            L)))))
              (And
                (∀ (s : ProjRescale.MaxSupport.A2State n),
                  @Relation.ReflTransGen (ProjRescale.MaxSupport.A2State n) (@ProjRescale.MaxSupport.A2Step n L)
                      (ProjRescale.MaxSupport.A2Init n) s →
                    @LE.le Nat instLENat (@ProjRescale.MaxSupport.A2State.rescalings n s)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (ProjRescale.MaxSupport.kIter
                                (@Min.min Real Real.instMin (@ProjRescale.MaxSupport.condMeasure n L)
                                  (@ProjRescale.MaxSupport.condMeasure n
                                    (@Submodule.orthogonal Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                                      (@PiLp.normedAddCommGroup
                                        (@OfNat.ofNat ENNReal (nat_lit 2)
                                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                            (@AddMonoidWithOne.toNatCast ENNReal
                                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                                ENNReal.instAddCommMonoidWithOne))
                                            PiLp.innerProductSpace._proof_1))
                                        (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                        fun (i : Fin n) => Real.normedAddCommGroup)
                                      (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                                        (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup)
                                        fun (i : Fin n) => @RCLike.toInnerProductSpaceReal Real Real.instRCLike)
                                      L)))))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (ProjRescale.MaxSupport.kIter
                            (@Min.min Real Real.instMin (@ProjRescale.MaxSupport.condMeasure n L)
                              (@ProjRescale.MaxSupport.condMeasure n
                                (@Submodule.orthogonal Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                                  (@PiLp.normedAddCommGroup
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                    fun (i : Fin n) => Real.normedAddCommGroup)
                                  (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                                    (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup)
                                    fun (i : Fin n) => @RCLike.toInnerProductSpaceReal Real Real.instRCLike)
                                  L)))))))
                (∀ (i R : Nat) (x : ProjRescale.MaxSupport.E n) (J : Finset (Fin n)) (xh : ProjRescale.MaxSupport.E n)
                  (Jh : Finset (Fin n)),
                  @Relation.ReflTransGen (ProjRescale.MaxSupport.A2State n) (@ProjRescale.MaxSupport.A2Step n L)
                      (ProjRescale.MaxSupport.A2Init n) (@ProjRescale.MaxSupport.A2State.done n i R x J xh Jh) →
                    And
                      (And (@Eq (Finset (Fin n)) J (@ProjRescale.MaxSupport.maxSupp n L))
                        (And
                          (@Membership.mem (ProjRescale.MaxSupport.E n)
                            (@Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
                              (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                (@WithLp.instAddCommGroup
                                  (@OfNat.ofNat ENNReal (nat_lit 2)
                                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                      (@AddMonoidWithOne.toNatCast ENNReal
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                          ENNReal.instAddCommMonoidWithOne))
                                      PiLp.innerProductSpace._proof_1))
                                  ((i : Fin n) → (fun (x : Fin n) => Real) i)
                                  (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)))
                              (@WithLp.instModule
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    PiLp.innerProductSpace._proof_1))
                                Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                                (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                  Real.instAddCommGroup)
                                (@Pi.Function.module (Fin n) Real Real Real.semiring
                                  (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                                  (@Semiring.toModule Real Real.semiring))))
                            (@SetLike.instMembership
                              (@Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
                                (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                  (@WithLp.instAddCommGroup
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    ((i : Fin n) → (fun (x : Fin n) => Real) i)
                                    (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup)))
                                (@WithLp.instModule
                                  (@OfNat.ofNat ENNReal (nat_lit 2)
                                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                      (@AddMonoidWithOne.toNatCast ENNReal
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                          ENNReal.instAddCommMonoidWithOne))
                                      PiLp.innerProductSpace._proof_1))
                                  Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                                  (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module (Fin n) Real Real Real.semiring
                                    (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                                    (@Semiring.toModule Real Real.semiring))))
                              (ProjRescale.MaxSupport.E n)
                              (@Submodule.setLike Real (ProjRescale.MaxSupport.E n) Real.semiring
                                (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                  (@WithLp.instAddCommGroup
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    ((i : Fin n) → (fun (x : Fin n) => Real) i)
                                    (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup)))
                                (@WithLp.instModule
                                  (@OfNat.ofNat ENNReal (nat_lit 2)
                                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                      (@AddMonoidWithOne.toNatCast ENNReal
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                          ENNReal.instAddCommMonoidWithOne))
                                      PiLp.innerProductSpace._proof_1))
                                  Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                                  (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module (Fin n) Real Real Real.semiring
                                    (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                                    (@Semiring.toModule Real Real.semiring)))))
                            L x)
                          (And
                            (@Membership.mem (ProjRescale.MaxSupport.E n) (Set (ProjRescale.MaxSupport.E n))
                              (@Set.instMembership (ProjRescale.MaxSupport.E n)) (ProjRescale.MaxSupport.nonneg n) x)
                            (∀ (j : Fin n),
                              @Membership.mem (Fin n) (Finset (Fin n))
                                  (@SetLike.instMembership (Finset (Fin n)) (Fin n) (@Finset.instSetLike (Fin n))) J j →
                                @LT.lt ((fun (x : Fin n) => Real) j) Real.instLT
                                  (@OfNat.ofNat ((fun (x : Fin n) => Real) j) (nat_lit 0)
                                    (@Zero.toOfNat0 ((fun (x : Fin n) => Real) j) Real.instZero))
                                  (@WithLp.ofLp
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    ((i : Fin n) → (fun (x : Fin n) => Real) i) x j)))))
                      (And
                        (@Eq (Finset (Fin n)) Jh
                          (@ProjRescale.MaxSupport.maxSupp n
                            (@Submodule.orthogonal Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                              (@PiLp.normedAddCommGroup
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    PiLp.innerProductSpace._proof_1))
                                (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                fun (i : Fin n) => Real.normedAddCommGroup)
                              (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                                (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup) fun (i : Fin n) =>
                                @RCLike.toInnerProductSpaceReal Real Real.instRCLike)
                              L)))
                        (And
                          (@Membership.mem (ProjRescale.MaxSupport.E n)
                            (@Submodule Real (ProjRescale.MaxSupport.E n)
                              (@DivisionSemiring.toSemiring Real
                                (@Semifield.toDivisionSemiring Real
                                  (@Field.toSemifield Real
                                    (@NormedField.toField Real
                                      (@DenselyNormedField.toNormedField Real
                                        (@RCLike.toDenselyNormedField Real Real.instRCLike))))))
                              (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                (@NormedAddCommGroup.toAddCommGroup (ProjRescale.MaxSupport.E n)
                                  (@PiLp.normedAddCommGroup
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                    fun (i : Fin n) => Real.normedAddCommGroup)))
                              (@NormedSpace.toModule Real (ProjRescale.MaxSupport.E n)
                                (@DenselyNormedField.toNormedField Real
                                  (@RCLike.toDenselyNormedField Real Real.instRCLike))
                                (@NormedAddCommGroup.toSeminormedAddCommGroup (ProjRescale.MaxSupport.E n)
                                  (@PiLp.normedAddCommGroup
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                    fun (i : Fin n) => Real.normedAddCommGroup))
                                (@InnerProductSpace.toNormedSpace Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup (ProjRescale.MaxSupport.E n)
                                    (@PiLp.normedAddCommGroup
                                      (@OfNat.ofNat ENNReal (nat_lit 2)
                                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                          (@AddMonoidWithOne.toNatCast ENNReal
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                              ENNReal.instAddCommMonoidWithOne))
                                          PiLp.innerProductSpace._proof_1))
                                      (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                      fun (i : Fin n) => Real.normedAddCommGroup))
                                  (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                                    (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup)
                                    fun (i : Fin n) => @RCLike.toInnerProductSpaceReal Real Real.instRCLike))))
                            (@SetLike.instMembership
                              (@Submodule Real (ProjRescale.MaxSupport.E n)
                                (@DivisionSemiring.toSemiring Real
                                  (@Semifield.toDivisionSemiring Real
                                    (@Field.toSemifield Real
                                      (@NormedField.toField Real
                                        (@DenselyNormedField.toNormedField Real
                                          (@RCLike.toDenselyNormedField Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                  (@NormedAddCommGroup.toAddCommGroup (ProjRescale.MaxSupport.E n)
                                    (@PiLp.normedAddCommGroup
                                      (@OfNat.ofNat ENNReal (nat_lit 2)
                                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                          (@AddMonoidWithOne.toNatCast ENNReal
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                              ENNReal.instAddCommMonoidWithOne))
                                          PiLp.innerProductSpace._proof_1))
                                      (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                      fun (i : Fin n) => Real.normedAddCommGroup)))
                                (@NormedSpace.toModule Real (ProjRescale.MaxSupport.E n)
                                  (@DenselyNormedField.toNormedField Real
                                    (@RCLike.toDenselyNormedField Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup (ProjRescale.MaxSupport.E n)
                                    (@PiLp.normedAddCommGroup
                                      (@OfNat.ofNat ENNReal (nat_lit 2)
                                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                          (@AddMonoidWithOne.toNatCast ENNReal
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                              ENNReal.instAddCommMonoidWithOne))
                                          PiLp.innerProductSpace._proof_1))
                                      (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                      fun (i : Fin n) => Real.normedAddCommGroup))
                                  (@InnerProductSpace.toNormedSpace Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup (ProjRescale.MaxSupport.E n)
                                      (@PiLp.normedAddCommGroup
                                        (@OfNat.ofNat ENNReal (nat_lit 2)
                                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                            (@AddMonoidWithOne.toNatCast ENNReal
                                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                                ENNReal.instAddCommMonoidWithOne))
                                            PiLp.innerProductSpace._proof_1))
                                        (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                        fun (i : Fin n) => Real.normedAddCommGroup))
                                    (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                                      (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup)
                                      fun (i : Fin n) => @RCLike.toInnerProductSpaceReal Real Real.instRCLike))))
                              (ProjRescale.MaxSupport.E n)
                              (@Submodule.setLike Real (ProjRescale.MaxSupport.E n)
                                (@DivisionSemiring.toSemiring Real
                                  (@Semifield.toDivisionSemiring Real
                                    (@Field.toSemifield Real
                                      (@NormedField.toField Real
                                        (@DenselyNormedField.toNormedField Real
                                          (@RCLike.toDenselyNormedField Real Real.instRCLike))))))
                                (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                  (@NormedAddCommGroup.toAddCommGroup (ProjRescale.MaxSupport.E n)
                                    (@PiLp.normedAddCommGroup
                                      (@OfNat.ofNat ENNReal (nat_lit 2)
                                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                          (@AddMonoidWithOne.toNatCast ENNReal
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                              ENNReal.instAddCommMonoidWithOne))
                                          PiLp.innerProductSpace._proof_1))
                                      (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                      fun (i : Fin n) => Real.normedAddCommGroup)))
                                (@NormedSpace.toModule Real (ProjRescale.MaxSupport.E n)
                                  (@DenselyNormedField.toNormedField Real
                                    (@RCLike.toDenselyNormedField Real Real.instRCLike))
                                  (@NormedAddCommGroup.toSeminormedAddCommGroup (ProjRescale.MaxSupport.E n)
                                    (@PiLp.normedAddCommGroup
                                      (@OfNat.ofNat ENNReal (nat_lit 2)
                                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                          (@AddMonoidWithOne.toNatCast ENNReal
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                              ENNReal.instAddCommMonoidWithOne))
                                          PiLp.innerProductSpace._proof_1))
                                      (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                      fun (i : Fin n) => Real.normedAddCommGroup))
                                  (@InnerProductSpace.toNormedSpace Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                                    (@NormedAddCommGroup.toSeminormedAddCommGroup (ProjRescale.MaxSupport.E n)
                                      (@PiLp.normedAddCommGroup
                                        (@OfNat.ofNat ENNReal (nat_lit 2)
                                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                            (@AddMonoidWithOne.toNatCast ENNReal
                                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                                ENNReal.instAddCommMonoidWithOne))
                                            PiLp.innerProductSpace._proof_1))
                                        (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                        fun (i : Fin n) => Real.normedAddCommGroup))
                                    (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                                      (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup)
                                      fun (i : Fin n) => @RCLike.toInnerProductSpaceReal Real Real.instRCLike)))))
                            (@Submodule.orthogonal Real (ProjRescale.MaxSupport.E n) Real.instRCLike
                              (@PiLp.normedAddCommGroup
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    PiLp.innerProductSpace._proof_1))
                                (Fin n) (fun (x : Fin n) => Real) fact_one_le_two_ennreal (Fin.fintype n)
                                fun (i : Fin n) => Real.normedAddCommGroup)
                              (@PiLp.innerProductSpace Real Real.instRCLike (Fin n) (Fin.fintype n)
                                (fun (x : Fin n) => Real) (fun (i : Fin n) => Real.normedAddCommGroup) fun (i : Fin n) =>
                                @RCLike.toInnerProductSpaceReal Real Real.instRCLike)
                              L)
                            xh)
                          (And
                            (@Membership.mem (ProjRescale.MaxSupport.E n) (Set (ProjRescale.MaxSupport.E n))
                              (@Set.instMembership (ProjRescale.MaxSupport.E n)) (ProjRescale.MaxSupport.nonneg n) xh)
                            (∀ (j : Fin n),
                              @Membership.mem (Fin n) (Finset (Fin n))
                                  (@SetLike.instMembership (Finset (Fin n)) (Fin n) (@Finset.instSetLike (Fin n))) Jh j →
                                @LT.lt ((fun (x : Fin n) => Real) j) Real.instLT
                                  (@OfNat.ofNat ((fun (x : Fin n) => Real) j) (nat_lit 0)
                                    (@Zero.toOfNat0 ((fun (x : Fin n) => Real) j) Real.instZero))
                                  (@WithLp.ofLp
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    ((i : Fin n) → (fun (x : Fin n) => Real) i) xh j)))))))))
) := @Queelius.ProjectionRescaling.outer_root

end

section
noncomputable section
namespace Queelius.ProjectionRescaling
open Finset Classical ProjRescale.MaxSupport

theorem lift_left_call {n : ℕ} (L : Submodule ℝ (E n)) (i R : ℕ) (σ : ℝ)
    {a b : A1State n} (h : Relation.ReflTransGen (A1Step L σ) a b) :
    Relation.ReflTransGen (A2Step L) (.callL i σ R a) (.callL i σ R b) := by
  induction h with
  | refl => rfl
  | tail h hs ih => exact ih.tail (A2Step.stepL i σ R _ _ hs)

theorem lift_right_call {n : ℕ} (L : Submodule ℝ (E n)) (i R : ℕ) (σ : ℝ)
    (x : E n) (J : Finset (Fin n)) {a b : A1State n}
    (h : Relation.ReflTransGen (A1Step Lᗮ σ) a b) :
    Relation.ReflTransGen (A2Step L) (.callLperp i σ R x J a) (.callLperp i σ R x J b) := by
  induction h with
  | refl => rfl
  | tail h hs ih => exact ih.tail (A2Step.stepLperp i σ R x J _ _ hs)

namespace Controls
theorem corrected_iteration_at_one : kIter 1=1 := by norm_num [kIter,Real.logb]
theorem guess_schedule_first_three : outerGuess 1=1/2 ∧ outerGuess 2=1/4 ∧ outerGuess 3=1/16 := by
  norm_num [outerGuess]
theorem full_space_outer_two_rescalings :
    Relation.ReflTransGen (A2Step (⊤:Submodule ℝ (E 1))) (A2Init 1)
      (.done 1 2 (WithLp.toLp 2 (fun _=>1)) univ 0 ∅) := by
  let u : E 1 := WithLp.toLp 2 (fun _=>1)
  have hd : diagScale (fun _ : Fin 1 => (1:ℝ)) (⊤:Submodule ℝ (E 1))=⊤ := by
    simp [diagScale]
  have hcoord : coordSub (univ:Finset (Fin 1))=(⊤:Submodule ℝ (E 1)) := by
    ext x
    simp [coordSub]
  have hp : projDLJ (⊤:Submodule ℝ (E 1)) (fun _=>1) univ u=u := by
    apply Submodule.starProjection_eq_self_iff.mpr
    change u ∈ diagScale (fun _ : Fin 1 => (1:ℝ)) (⊤:Submodule ℝ (E 1)) ⊓ coordSub univ
    rw [hd,hcoord]
    trivial
  have hf : A1Step (⊤:Submodule ℝ (E 1)) (1/2) (A1Init 1) (.halt u univ 0) := by
    have hh:=A1Step.found (L:=(⊤:Submodule ℝ (E 1))) (σ:=(1/2))
      (fun _=>1) univ 0 u (by simp [u,simplexJ]) (by intro j hj;rw [hp];norm_num [u])
    rw [hp] at hh
    simpa only [A1Init,u,inv_one,one_mul] using hh
  have hstart := lift_left_call (⊤:Submodule ℝ (E 1)) 1 0 (1/2) (Relation.ReflTransGen.single hf)
  have hret:=hstart.tail (A2Step.retL 1 (1/2) 0 u univ 0)
  have hz : A1Halts (⊤:Submodule ℝ (E 1))ᗮ (1/2) 0 ∅ 2 := by
    simpa using zero_subspace_two_rescalings
  have hright:=lift_right_call (⊤:Submodule ℝ (E 1)) 1 0 (1/2) u univ hz
  have hfinal := (hret.trans hright).tail (A2Step.halt 1 (1/2) 0 u univ 0 ∅ 2 (by simp))
  exact hfinal

theorem corrected_bound_at_one_positive : 2*1*(2^kIter 1-1+kIter 1)=4 := by
  norm_num [corrected_iteration_at_one]
end Controls
end Queelius.ProjectionRescaling

end


theorem solution : (
  ∀ (n : Nat),
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
      ∀
        (L :
          @Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
            (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
              (@WithLp.instAddCommGroup
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    PiLp.innerProductSpace._proof_1))
                ((i : Fin n) → (fun (x : Fin n) => Real) i)
                (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)))
            (@WithLp.instModule
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  PiLp.innerProductSpace._proof_1))
              Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
              (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) => Real.instAddCommGroup)
              (@Pi.Function.module (Fin n) Real Real Real.semiring
                (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                (@Semiring.toModule Real Real.semiring))))
        (σ : Real),
        @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) σ →
          @LT.lt Real Real.instLT σ (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) →
            And
              (∀ (s : ProjRescale.MaxSupport.A1State n),
                @Relation.ReflTransGen (ProjRescale.MaxSupport.A1State n) (@ProjRescale.MaxSupport.A1Step n L σ)
                    (ProjRescale.MaxSupport.A1Init n) s →
                  @ProjRescale.MaxSupport.A1State.IsRun n s →
                    @Exists (ProjRescale.MaxSupport.A1State n) fun (s' : ProjRescale.MaxSupport.A1State n) =>
                      @ProjRescale.MaxSupport.A1Step n L σ s s')
              (And
                (Not
                  (@Exists (Nat → ProjRescale.MaxSupport.A1State n) fun (f : Nat → ProjRescale.MaxSupport.A1State n) =>
                    And
                      (@Eq (ProjRescale.MaxSupport.A1State n)
                        (f (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (ProjRescale.MaxSupport.A1Init n))
                      (∀ (t : Nat),
                        @ProjRescale.MaxSupport.A1Step n L σ (f t)
                          (f
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) t
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (And
                  (∀ (s : ProjRescale.MaxSupport.A1State n),
                    @Relation.ReflTransGen (ProjRescale.MaxSupport.A1State n) (@ProjRescale.MaxSupport.A1Step n L σ)
                        (ProjRescale.MaxSupport.A1Init n) s →
                      @LE.le Nat instLENat (@ProjRescale.MaxSupport.A1State.rescalings n s)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@Nat.floor Real Real.semiring Real.partialOrder
                              (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing)
                              (Real.logb
                                (@OfNat.ofNat Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                (@HDiv.hDiv Real Real Real
                                  (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) σ)))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (∀ (x : ProjRescale.MaxSupport.E n) (J : Finset (Fin n)) (r : Nat),
                      @ProjRescale.MaxSupport.A1Halts n L σ x J r →
                        And
                          (@Membership.mem (ProjRescale.MaxSupport.E n)
                            (@Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
                              (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                (@WithLp.instAddCommGroup
                                  (@OfNat.ofNat ENNReal (nat_lit 2)
                                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                      (@AddMonoidWithOne.toNatCast ENNReal
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                          ENNReal.instAddCommMonoidWithOne))
                                      PiLp.innerProductSpace._proof_1))
                                  ((i : Fin n) → (fun (x : Fin n) => Real) i)
                                  (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)))
                              (@WithLp.instModule
                                (@OfNat.ofNat ENNReal (nat_lit 2)
                                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                    (@AddMonoidWithOne.toNatCast ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                                    PiLp.innerProductSpace._proof_1))
                                Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                                (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                  Real.instAddCommGroup)
                                (@Pi.Function.module (Fin n) Real Real Real.semiring
                                  (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                                  (@Semiring.toModule Real Real.semiring))))
                            (@SetLike.instMembership
                              (@Submodule Real (ProjRescale.MaxSupport.E n) Real.semiring
                                (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                  (@WithLp.instAddCommGroup
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    ((i : Fin n) → (fun (x : Fin n) => Real) i)
                                    (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup)))
                                (@WithLp.instModule
                                  (@OfNat.ofNat ENNReal (nat_lit 2)
                                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                      (@AddMonoidWithOne.toNatCast ENNReal
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                          ENNReal.instAddCommMonoidWithOne))
                                      PiLp.innerProductSpace._proof_1))
                                  Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                                  (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module (Fin n) Real Real Real.semiring
                                    (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                                    (@Semiring.toModule Real Real.semiring))))
                              (ProjRescale.MaxSupport.E n)
                              (@Submodule.setLike Real (ProjRescale.MaxSupport.E n) Real.semiring
                                (@AddCommGroup.toAddCommMonoid (ProjRescale.MaxSupport.E n)
                                  (@WithLp.instAddCommGroup
                                    (@OfNat.ofNat ENNReal (nat_lit 2)
                                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                        (@AddMonoidWithOne.toNatCast ENNReal
                                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                            ENNReal.instAddCommMonoidWithOne))
                                        PiLp.innerProductSpace._proof_1))
                                    ((i : Fin n) → (fun (x : Fin n) => Real) i)
                                    (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                      Real.instAddCommGroup)))
                                (@WithLp.instModule
                                  (@OfNat.ofNat ENNReal (nat_lit 2)
                                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                      (@AddMonoidWithOne.toNatCast ENNReal
                                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                          ENNReal.instAddCommMonoidWithOne))
                                      PiLp.innerProductSpace._proof_1))
                                  Real ((i : Fin n) → (fun (x : Fin n) => Real) i) Real.semiring
                                  (@Pi.addCommGroup (Fin n) (fun (x : Fin n) => Real) fun (i : Fin n) =>
                                    Real.instAddCommGroup)
                                  (@Pi.Function.module (Fin n) Real Real Real.semiring
                                    (@Semiring.toAddCommMonoid Real (@Ring.toSemiring Real Real.instRing))
                                    (@Semiring.toModule Real Real.semiring)))))
                            L x)
                          (And
                            (@Membership.mem (ProjRescale.MaxSupport.E n) (Set (ProjRescale.MaxSupport.E n))
                              (@Set.instMembership (ProjRescale.MaxSupport.E n)) (ProjRescale.MaxSupport.nonneg n) x)
                            (And
                              (∀ (j : Fin n),
                                @Membership.mem (Fin n) (Finset (Fin n))
                                    (@SetLike.instMembership (Finset (Fin n)) (Fin n) (@Finset.instSetLike (Fin n))) J j →
                                  @LT.lt ((fun (x : Fin n) => Real) j) Real.instLT
                                    (@OfNat.ofNat ((fun (x : Fin n) => Real) j) (nat_lit 0)
                                      (@Zero.toOfNat0 ((fun (x : Fin n) => Real) j) Real.instZero))
                                    (@WithLp.ofLp
                                      (@OfNat.ofNat ENNReal (nat_lit 2)
                                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                                          (@AddMonoidWithOne.toNatCast ENNReal
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal
                                              ENNReal.instAddCommMonoidWithOne))
                                          PiLp.innerProductSpace._proof_1))
                                      ((i : Fin n) → (fun (x : Fin n) => Real) i) x j))
                              (@LE.le (Finset (Fin n))
                                (@Preorder.toLE (Finset (Fin n))
                                  (@PartialOrder.toPreorder (Finset (Fin n)) (@Finset.instPartialOrder (Fin n))))
                                J (@ProjRescale.MaxSupport.maxSupp n L)))))
                    (@LE.le Real Real.instLE σ (@ProjRescale.MaxSupport.condMeasure n L) →
                      ∀ (x : ProjRescale.MaxSupport.E n) (J : Finset (Fin n)) (r : Nat),
                        @ProjRescale.MaxSupport.A1Halts n L σ x J r →
                          And (@Eq (Finset (Fin n)) J (@ProjRescale.MaxSupport.maxSupp n L))
                            (@LE.le Nat instLENat r
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@Finset.sum (Fin n) Nat Nat.instAddCommMonoid (@ProjRescale.MaxSupport.maxSupp n L)
                                  fun (j : Fin n) =>
                                  @Nat.ceil Real Real.semiring Real.partialOrder
                                    (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing)
                                    (Real.logb
                                      (@OfNat.ofNat Real (nat_lit 2)
                                        (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                                          (@Nat.instAtLeastTwoHAddOfNat
                                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                            (@Nat.instNeZeroSucc
                                              (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                      (@HDiv.hDiv Real Real Real
                                        (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                                        (@ProjRescale.MaxSupport.sigmaI n L j))))
                                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n
                                    (@Finset.card (Fin n) (@ProjRescale.MaxSupport.maxSupp n L)))
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@Nat.floor Real Real.semiring Real.partialOrder
                                      (@FloorRing.toFloorSemiring Real Real.instRing Real.linearOrder Real.instFloorRing)
                                      (Real.logb
                                        (@OfNat.ofNat Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                        (@HDiv.hDiv Real Real Real
                                          (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                                          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) σ)))
                                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))
) := @ProjRescale.MaxSupport.proposition_1
