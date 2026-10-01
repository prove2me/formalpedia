-- Prove2me | solution 1 for TierneyMH.Peskun.variance_identity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:18:40.422983+00:00
-- url     : https://prove2.me/submissions/8a3f05d2-db87-4af5-bb3f-e2bafbeb5fe1

import Definitions.Def_TierneyMH_Peskun_chainMeasure
import Definitions.Def_TierneyMH_Peskun_lagInner
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open TierneyMH.Peskun

namespace PeskunProof
variable {E : Type*} [MeasurableSpace E]

theorem fst_preserving (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] : MeasurePreserving Prod.fst (π ⊗ₘ P) π :=
  ⟨measurable_fst, Measure.fst_compProd π P⟩

theorem snd_preserving (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π) :
    MeasurePreserving Prod.snd (π ⊗ₘ P) π :=
  ⟨measurable_snd, (Measure.snd_compProd π P).trans hi⟩

theorem integral_preserving {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (T : A → B) (hT : MeasurePreserving T μ ν)
    (g : B → ℝ) (hg : Measurable g) : ∫ x, g (T x) ∂μ = ∫ y, g y ∂ν := by
  calc
    ∫ x, g (T x) ∂μ = ∫ y, g y ∂μ.map T :=
      (integral_map hT.measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = ∫ y, g y ∂ν := by rw [hT.map_eq]

theorem joint_memLp (π : Measure E) [IsProbabilityMeasure π]
    (P : Kernel E E) [IsMarkovKernel P] (hi : Kernel.Invariant P π)
    (f : E → ℝ) (hf : MemLp f 2 π) :
    MemLp (fun p : E × E => f p.1) 2 (π ⊗ₘ P) ∧
      MemLp (fun p : E × E => f p.2) 2 (π ⊗ₘ P) :=
  ⟨hf.comp_measurePreserving (fst_preserving π P),hf.comp_measurePreserving (snd_preserving π P hi)⟩

end PeskunProof

namespace PeskunChain
variable {E : Type*} [MeasurableSpace E]

instance (π : Measure E) [IsProbabilityMeasure π] (H : Kernel E E) [IsMarkovKernel H] :
    IsProbabilityMeasure (chainMeasure π H) := by unfold chainMeasure; infer_instance

theorem initial (π : Measure E) (H : Kernel E E) [IsMarkovKernel H] :
    (chainMeasure π H).map (fun ω => ω 0)=π := by
  let κ := fun n : ℕ => H.comap (fun x : (Π _ : Finset.Iic n, E) => x ⟨n,Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)
  change (Kernel.trajMeasure (X := fun _ => E) π κ).map (fun ω => ω 0)=π
  have he : (fun ω : ℕ → E => ω 0) =
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => E)) ∘ (Preorder.frestrictLe 0) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [Kernel.trajMeasure,Measure.map_comp _ _ (by fun_prop),Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self,Measure.id_comp]
  exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => E)).symm.map_symm_map (μ := π)

theorem projection_step (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (i j : ℕ) (hij : i ≤ j) :
    (chainMeasure π H).map (fun ω => (ω i,ω (j+1))) =
      (Kernel.id ∥ₖ H) ∘ₘ (chainMeasure π H).map (fun ω => (ω i,ω j)) := by
  let P := chainMeasure π H
  let g := fun x : (Π _ : Finset.Iic j, E) => x ⟨j,Finset.mem_Iic.mpr le_rfl⟩
  let f := fun x : (Π _ : Finset.Iic j, E) => x ⟨i,Finset.mem_Iic.mpr hij⟩
  have hf : Measurable f := measurable_pi_apply _
  have hg : Measurable g := measurable_pi_apply _
  have hhist : P.map (Preorder.frestrictLe j) ⊗ₘ H.comap g hg =
      P.map (fun ω => (Preorder.frestrictLe j ω,ω (j+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hleft : P.map (fun ω => (ω i,ω (j+1))) =
      (P.map (Preorder.frestrictLe j) ⊗ₘ H.comap g hg).map (Prod.map f id) := by
    rw [hhist,Measure.map_map (hf.prodMap measurable_id) (by fun_prop)]
    rfl
  have hright : P.map (fun ω => (ω i,ω j)) =
      (P.map (Preorder.frestrictLe j)).map (fun x => (f x,g x)) := by
    rw [Measure.map_map (hf.prodMk hg) (by fun_prop)]
    rfl
  change P.map (fun ω => (ω i,ω (j+1))) = (Kernel.id ∥ₖ H) ∘ₘ P.map (fun ω => (ω i,ω j))
  rw [hleft,hright,Measure.compProd_eq_comp_prod,Measure.map_comp _ _ (hf.prodMap measurable_id),
    ← Kernel.map_prod_eq _ _ hf,Kernel.id_map hf,
    ← Measure.deterministic_comp_eq_map (hf.prodMk hg),Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap]
  congr 1
  ext x
  simp only [Kernel.prod_apply,Kernel.deterministic_apply,Kernel.comap_apply,
    Kernel.parallelComp_apply,Kernel.id_apply]

theorem marginal_step (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (j : ℕ) :
    (chainMeasure π H).map (fun ω => ω (j+1)) = H ∘ₘ (chainMeasure π H).map (fun ω => ω j) := by
  let P := chainMeasure π H
  let g := fun x : (Π _ : Finset.Iic j, E) => x ⟨j,Finset.mem_Iic.mpr le_rfl⟩
  have hg : Measurable g := measurable_pi_apply _
  have hhist : P.map (Preorder.frestrictLe j) ⊗ₘ H.comap g hg =
      P.map (fun ω => (Preorder.frestrictLe j ω,ω (j+1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hh := congrArg (fun μ : Measure ((Π _ : Finset.Iic j,E) × E) => μ.snd) hhist
  rw [Measure.snd_compProd] at hh
  have he : (P.map (fun ω => (Preorder.frestrictLe j ω,ω (j+1)))).snd =
      P.map (fun ω => ω (j+1)) := by
    rw [Measure.snd,Measure.map_map measurable_snd (by fun_prop)]
    rfl
  rw [he] at hh
  change P.map (fun ω => ω (j+1))=H ∘ₘ P.map (fun ω => ω j)
  rw [← hh,← Kernel.comp_deterministic_eq_comap _ hg,← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hg,Measure.map_map hg (by fun_prop)]
  rfl

theorem marginal (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π) (j : ℕ) :
    (chainMeasure π H).map (fun ω => ω j)=π := by
  induction j with
  | zero => exact initial π H
  | succ j ih => rw [marginal_step,ih]; exact hi

instance markov_pow (H : Kernel E E) [IsMarkovKernel H] (k : ℕ) : IsMarkovKernel (H^k) := by
  induction k with
  | zero => change IsMarkovKernel Kernel.id; infer_instance
  | succ k ih =>
    letI := ih
    rw [show k+1=1+k by omega,Kernel.pow_add,pow_one]
    infer_instance

theorem invariant_pow (π : Measure E) (H : Kernel E E) [IsMarkovKernel H]
    (hi : Kernel.Invariant H π) (k : ℕ) : Kernel.Invariant (H^k) π := by
  induction k with
  | zero => exact Measure.id_comp
  | succ k ih =>
    rw [show k+1=1+k by omega,Kernel.pow_add,pow_one]
    exact hi.comp ih

theorem joint (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π) (i k : ℕ) :
    (chainMeasure π H).map (fun ω => (ω i,ω (i+k)))=π ⊗ₘ (H^k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    change (chainMeasure π H).map (fun ω => (ω i,ω (i+0)))=π ⊗ₘ Kernel.id
    rw [Measure.compProd_id]
    calc
      _ = ((chainMeasure π H).map (fun ω => ω i)).map Function.diag := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      _ = π.map Function.diag := by rw [marginal π H hi i]
  | succ k ih =>
    rw [show i+(k+1)=(i+k)+1 by omega,projection_step π H i (i+k) (by omega),ih,
      Measure.parallelComp_comp_compProd,show k+1=1+k by omega,Kernel.pow_add,pow_one]

theorem coordinate_preserving (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π) (i : ℕ) :
    MeasurePreserving (fun ω : ℕ → E => ω i) (chainMeasure π H) π :=
  ⟨measurable_pi_apply i,marginal π H hi i⟩

theorem correlation (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) (i k : ℕ) :
    (∫ ω, f (ω i)*f (ω (i+k)) ∂chainMeasure π H)=lagInner π H f k := by
  have hpair := PeskunProof.joint_memLp π (H^k) (invariant_pow π H hi k) f hf
  calc
    _ = ∫ p : E × E, f p.1*f p.2 ∂π ⊗ₘ (H^k) :=
      PeskunProof.integral_preserving _ _ _ ⟨by fun_prop,joint π H hi i k⟩ _ (by fun_prop)
    _ = lagInner π H f k := by
      have hp : Integrable (fun p : E × E => f p.1*f p.2) (π ⊗ₘ (H^k)) := hpair.1.integrable_mul hpair.2
      rw [Measure.integral_compProd hp]
      simp only [lagInner,integral_const_mul]

theorem covariance_lag (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hi : Kernel.Invariant H π)
    (f : E → ℝ) (hm : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π=0) (i j : ℕ) :
    covariance (fun ω => f (ω i)) (fun ω => f (ω j)) (chainMeasure π H)=lagInner π H f (Nat.dist i j) := by
  have hcoord (i : ℕ) : MemLp (fun ω => f (ω i)) 2 (chainMeasure π H) :=
    hf.comp_measurePreserving (coordinate_preserving π H hi i)
  have hmean (i : ℕ) : (∫ ω, f (ω i) ∂chainMeasure π H)=0 :=
    (PeskunProof.integral_preserving _ _ _ (coordinate_preserving π H hi i) f hm).trans hf0
  rw [covariance_eq_sub (hcoord i) (hcoord j),hmean i,hmean j]
  simp only [zero_mul,sub_zero,Pi.mul_apply]
  by_cases hij : i ≤ j
  · rw [Nat.dist_eq_sub_of_le hij]
    convert! correlation π H hi f hm hf i (j-i) using 1
    rw [Nat.add_sub_of_le hij]
  · have hji : j ≤ i := by omega
    rw [Nat.dist_eq_sub_of_le_right hji]
    have hh := correlation π H hi f hm hf j (i-j)
    rw [Nat.add_sub_of_le hji] at hh
    simpa only [mul_comm] using hh

theorem lag_zero (π : Measure E) (H : Kernel E E) (f : E → ℝ) (hm : Measurable f) :
    lagInner π H f 0=∫ x, f x^2 ∂π := by
  change (∫ x, f x * ∫ y, f y ∂Kernel.id x ∂π)=_
  simp only [Kernel.id_apply,integral_dirac' _ _ hm.stronglyMeasurable,pow_two]

end PeskunChain

open Finset
namespace TierneyFiniteSum
 theorem reflected_Icc (c : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Icc 1 n, c (n+1-i)) = ∑ i ∈ Icc 1 n, c i := by
  refine sum_nbij' (fun i => n+1-i) (fun i => n+1-i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [mem_Icc] at hi ⊢
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    omega
  · intro i hi
    simp only [mem_Icc] at hi
    omega
  · intro i hi
    rfl
 theorem covariance_sum (c : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n, c (Nat.dist i j)) =
      (n:ℝ)*c 0+2*∑ k ∈ Icc 1 n, ((n:ℝ)-k)*c k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrow : (∑ i ∈ Icc 1 n, c (Nat.dist i (n+1))) = ∑ i ∈ Icc 1 n, c i := by
      calc
        _ = ∑ i ∈ Icc 1 n, c (n+1-i) := by
          apply sum_congr rfl
          intro i hi
          rw [Nat.dist_eq_sub_of_le (by have := (mem_Icc.mp hi).2; omega)]
        _ = _ := reflected_Icc c n
    have hcol : (∑ i ∈ Icc 1 n, c (Nat.dist (n+1) i)) = ∑ i ∈ Icc 1 n, c i := by
      simpa only [Nat.dist_comm] using hrow
    have hw : (∑ k ∈ Icc 1 (n+1), (((n+1:ℕ):ℝ)-k)*c k) =
        (∑ k ∈ Icc 1 n, ((n:ℝ)-k)*c k)+(∑ k ∈ Icc 1 n, c k) := by
      rw [sum_Icc_succ_top (by omega)]
      simp only [sub_self, zero_mul, add_zero]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      push_cast
      ring
    rw [hw, sum_Icc_succ_top (by omega)]
    simp_rw [sum_Icc_succ_top (by omega : 1 ≤ n+1)]
    rw [sum_add_distrib, ih, hrow, hcol]
    simp only [Nat.dist_self, Nat.cast_add, Nat.cast_one]
    ring
end TierneyFiniteSum
open TierneyMH.Peskun
open Filter

theorem solution {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (H : Kernel E E) [IsMarkovKernel H] (hH : Kernel.IsReversible H π)
    (f : E → ℝ) (hf_meas : Measurable f) (hf : MemLp f 2 π) (hf0 : ∫ x, f x ∂π = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    variance (pathSum f n) (chainMeasure π H) / n =
      ∫ x, f x ^ 2 ∂π +
        2 * ∑ i ∈ Finset.Icc 1 n, (((n : ℝ) - i) / n) * lagInner π H f i := by
  have hi := hH.invariant
  have hcoord (i : ℕ) : MemLp (fun ω => f (ω i)) 2 (chainMeasure π H) :=
    hf.comp_measurePreserving (PeskunChain.coordinate_preserving π H hi i)
  have hv : variance (pathSum f n) (chainMeasure π H) =
      (n:ℝ)*lagInner π H f 0+2*∑ k ∈ Finset.Icc 1 n, ((n:ℝ)-k)*lagInner π H f k := by
    unfold pathSum
    rw [variance_fun_sum' (fun i _ => hcoord i)]
    simp_rw [PeskunChain.covariance_lag π H hi f hf_meas hf hf0]
    exact TierneyFiniteSum.covariance_sum _ n
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have he : (∑ k ∈ Finset.Icc 1 n, ((n:ℝ)-k)*lagInner π H f k)/(n:ℝ) =
      ∑ k ∈ Finset.Icc 1 n, (((n:ℝ)-k)/(n:ℝ))*lagInner π H f k := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hv,PeskunChain.lag_zero π H f hf_meas,add_div,mul_div_assoc 2,he]
  field_simp
