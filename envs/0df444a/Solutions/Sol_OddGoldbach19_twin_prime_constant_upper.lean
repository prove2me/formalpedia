-- Prove2me | solution 1 for OddGoldbach19.twin_prime_constant_upper
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:14:36.603247+00:00
-- url     : https://prove2.me/submissions/c1cc6c52-d1bf-4024-b58d-4f3cc3069422

/- Finite-product upper-bound method adapted from public Apache2.0 Prove2Me
accepted proof91b4ca4a-771c-4be3-88cd-952059ec7610. The short prime-subset
certificate and tighter1.3204 bound are exact finite consequences. -/
import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
open scoped BigOperators
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
namespace TwinUpperShort
def rawQ (p : ℕ) : ℚ :=1-1/((p:ℚ)-1)^2
noncomputable def rawR (p : ℕ) : ℝ :=1-1/((p:ℝ)-1)^2
lemma cast_raw_prod (L : List ℕ) :
    (((L.map rawQ).prod:ℚ):ℝ)=(L.map rawR).prod := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons,List.prod_cons,Rat.cast_mul,ih]
    have hh : ((rawQ p:ℚ):ℝ)=rawR p := by
      unfold rawQ rawR
      push_cast
      norm_num
    rw [hh]
lemma twinPartial_fac_nonneg (p : ℕ) :
    (0 : ℝ) ≤ (if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  split_ifs with h
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by
      have : 3 ≤ p := by omega
      exact_mod_cast this
    have hden : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hle : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith)]
      exact hden
    linarith
  · norm_num

lemma twinPartial_fac_le_one (p : ℕ) :
    (if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ≤ 1 := by
  split_ifs with h
  · have hpos : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
    linarith
  · norm_num

lemma twinPartial_nonneg (Q : ℕ) : (0 : ℝ) ≤ TaoFivePrimes.twinPrimePartial Q := by
  rw [TaoFivePrimes.twinPrimePartial]
  exact Finset.prod_nonneg (fun p _ => twinPartial_fac_nonneg p)



end TwinUpperShort

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C0 : List ℕ :=[3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
theorem prime0 : ∀ p∈C0, p.Prime := by
  simp only [C0,List.forall_mem_cons]
  norm_num
theorem block0 : 0≤(C0.map rawR).prod ∧ (C0.map rawR).prod≤((166099838443/250000000000:ℚ):ℝ) := by
  have hQ : 0≤(C0.map rawQ).prod ∧ (C0.map rawQ).prod≤(166099838443/250000000000:ℚ) := by
    norm_num [C0,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C0.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C0.map rawQ).prod:ℚ):ℝ)≤((166099838443/250000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C1 : List ℕ :=[37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
theorem prime1 : ∀ p∈C1, p.Prime := by
  simp only [C1,List.forall_mem_cons]
  norm_num
theorem block1 : 0≤(C1.map rawR).prod ∧ (C1.map rawR).prod≤((3983998143/4000000000:ℚ):ℝ) := by
  have hQ : 0≤(C1.map rawQ).prod ∧ (C1.map rawQ).prod≤(3983998143/4000000000:ℚ) := by
    norm_num [C1,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C1.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C1.map rawQ).prod:ℚ):ℝ)≤((3983998143/4000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C2 : List ℕ :=[79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
theorem prime2 : ∀ p∈C2, p.Prime := by
  simp only [C2,List.forall_mem_cons]
  norm_num
theorem block2 : 0≤(C2.map rawR).prod ∧ (C2.map rawR).prod≤((62433513833/62500000000:ℚ):ℝ) := by
  have hQ : 0≤(C2.map rawQ).prod ∧ (C2.map rawQ).prod≤(62433513833/62500000000:ℚ) := by
    norm_num [C2,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C2.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C2.map rawQ).prod:ℚ):ℝ)≤((62433513833/62500000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C3 : List ℕ :=[131, 137, 139, 149, 151, 157, 163, 167, 173, 179]
theorem prime3 : ∀ p∈C3, p.Prime := by
  simp only [C3,List.forall_mem_cons]
  norm_num
theorem block3 : 0≤(C3.map rawR).prod ∧ (C3.map rawR).prod≤((999563391099/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C3.map rawQ).prod ∧ (C3.map rawQ).prod≤(999563391099/1000000000000:ℚ) := by
    norm_num [C3,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C3.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C3.map rawQ).prod:ℚ):ℝ)≤((999563391099/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C4 : List ℕ :=[181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
theorem prime4 : ∀ p∈C4, p.Prime := by
  simp only [C4,List.forall_mem_cons]
  norm_num
theorem block4 : 0≤(C4.map rawR).prod ∧ (C4.map rawR).prod≤((999762434407/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C4.map rawQ).prod ∧ (C4.map rawQ).prod≤(999762434407/1000000000000:ℚ) := by
    norm_num [C4,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C4.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C4.map rawQ).prod:ℚ):ℝ)≤((999762434407/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C5 : List ℕ :=[239, 241, 251, 257, 263, 269, 271, 277, 281, 283]
theorem prime5 : ∀ p∈C5, p.Prime := by
  simp only [C5,List.forall_mem_cons]
  norm_num
theorem block5 : 0≤(C5.map rawR).prod ∧ (C5.map rawR).prod≤((199970614001/200000000000:ℚ):ℝ) := by
  have hQ : 0≤(C5.map rawQ).prod ∧ (C5.map rawQ).prod≤(199970614001/200000000000:ℚ) := by
    norm_num [C5,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C5.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C5.map rawQ).prod:ℚ):ℝ)≤((199970614001/200000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C6 : List ℕ :=[293, 307, 311, 313, 317, 331, 337, 347, 349, 353]
theorem prime6 : ∀ p∈C6, p.Prime := by
  simp only [C6,List.forall_mem_cons]
  norm_num
theorem block6 : 0≤(C6.map rawR).prod ∧ (C6.map rawR).prod≤((49995209071/50000000000:ℚ):ℝ) := by
  have hQ : 0≤(C6.map rawQ).prod ∧ (C6.map rawQ).prod≤(49995209071/50000000000:ℚ) := by
    norm_num [C6,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C6.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C6.map rawQ).prod:ℚ):ℝ)≤((49995209071/50000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C7 : List ℕ :=[359, 367, 373, 379, 383, 389, 397, 401, 409, 419]
theorem prime7 : ∀ p∈C7, p.Prime := by
  simp only [C7,List.forall_mem_cons]
  norm_num
theorem block7 : 0≤(C7.map rawR).prod ∧ (C7.map rawR).prod≤((999932656469/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C7.map rawQ).prod ∧ (C7.map rawQ).prod≤(999932656469/1000000000000:ℚ) := by
    norm_num [C7,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C7.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C7.map rawQ).prod:ℚ):ℝ)≤((999932656469/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C8 : List ℕ :=[421, 431, 433, 439, 443, 449, 457, 461, 463, 467]
theorem prime8 : ∀ p∈C8, p.Prime := by
  simp only [C8,List.forall_mem_cons]
  norm_num
theorem block8 : 0≤(C8.map rawR).prod ∧ (C8.map rawR).prod≤((249987356679/250000000000:ℚ):ℝ) := by
  have hQ : 0≤(C8.map rawQ).prod ∧ (C8.map rawQ).prod≤(249987356679/250000000000:ℚ) := by
    norm_num [C8,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C8.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C8.map rawQ).prod:ℚ):ℝ)≤((249987356679/250000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C9 : List ℕ :=[479, 487, 491, 499, 503, 509, 521, 523, 541, 547]
theorem prime9 : ∀ p∈C9, p.Prime := by
  simp only [C9,List.forall_mem_cons]
  norm_num
theorem block9 : 0≤(C9.map rawR).prod ∧ (C9.map rawR).prod≤((999961197989/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C9.map rawQ).prod ∧ (C9.map rawQ).prod≤(999961197989/1000000000000:ℚ) := by
    norm_num [C9,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C9.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C9.map rawQ).prod:ℚ):ℝ)≤((999961197989/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C10 : List ℕ :=[557, 563, 569, 571, 577, 587, 593, 599, 601, 607]
theorem prime10 : ∀ p∈C10, p.Prime := by
  simp only [C10,List.forall_mem_cons]
  norm_num
theorem block10 : 0≤(C10.map rawR).prod ∧ (C10.map rawR).prod≤((999970345257/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C10.map rawQ).prod ∧ (C10.map rawQ).prod≤(999970345257/1000000000000:ℚ) := by
    norm_num [C10,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C10.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C10.map rawQ).prod:ℚ):ℝ)≤((999970345257/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C11 : List ℕ :=[613, 617, 619, 631, 641, 643, 647, 653, 659, 661]
theorem prime11 : ∀ p∈C11, p.Prime := by
  simp only [C11,List.forall_mem_cons]
  norm_num
theorem block11 : 0≤(C11.map rawR).prod ∧ (C11.map rawR).prod≤((24999383389/25000000000:ℚ):ℝ) := by
  have hQ : 0≤(C11.map rawQ).prod ∧ (C11.map rawQ).prod≤(24999383389/25000000000:ℚ) := by
    norm_num [C11,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C11.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C11.map rawQ).prod:ℚ):ℝ)≤((24999383389/25000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C12 : List ℕ :=[673, 677, 683, 691, 701, 709, 719, 727, 733, 739]
theorem prime12 : ∀ p∈C12, p.Prime := by
  simp only [C12,List.forall_mem_cons]
  norm_num
theorem block12 : 0≤(C12.map rawR).prod ∧ (C12.map rawR).prod≤((499989885971/500000000000:ℚ):ℝ) := by
  have hQ : 0≤(C12.map rawQ).prod ∧ (C12.map rawQ).prod≤(499989885971/500000000000:ℚ) := by
    norm_num [C12,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C12.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C12.map rawQ).prod:ℚ):ℝ)≤((499989885971/500000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C13 : List ℕ :=[743, 751, 757, 761, 769, 773, 787, 797, 809, 811]
theorem prime13 : ∀ p∈C13, p.Prime := by
  simp only [C13,List.forall_mem_cons]
  norm_num
theorem block13 : 0≤(C13.map rawR).prod ∧ (C13.map rawR).prod≤((999983298967/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C13.map rawQ).prod ∧ (C13.map rawQ).prod≤(999983298967/1000000000000:ℚ) := by
    norm_num [C13,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C13.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C13.map rawQ).prod:ℚ):ℝ)≤((999983298967/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C14 : List ℕ :=[821, 823, 827, 829, 839, 853, 857, 859, 863, 877]
theorem prime14 : ∀ p∈C14, p.Prime := by
  simp only [C14,List.forall_mem_cons]
  norm_num
theorem block14 : 0≤(C14.map rawR).prod ∧ (C14.map rawR).prod≤((999985934907/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C14.map rawQ).prod ∧ (C14.map rawQ).prod≤(999985934907/1000000000000:ℚ) := by
    norm_num [C14,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C14.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C14.map rawQ).prod:ℚ):ℝ)≤((999985934907/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C15 : List ℕ :=[881, 883, 887, 907, 911, 919, 929, 937, 941, 947]
theorem prime15 : ∀ p∈C15, p.Prime := by
  simp only [C15,List.forall_mem_cons]
  norm_num
theorem block15 : 0≤(C15.map rawR).prod ∧ (C15.map rawR).prod≤((6249924907/6250000000:ℚ):ℝ) := by
  have hQ : 0≤(C15.map rawQ).prod ∧ (C15.map rawQ).prod≤(6249924907/6250000000:ℚ) := by
    norm_num [C15,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C15.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C15.map rawQ).prod:ℚ):ℝ)≤((6249924907/6250000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C16 : List ℕ :=[953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019]
theorem prime16 : ∀ p∈C16, p.Prime := by
  simp only [C16,List.forall_mem_cons]
  norm_num
theorem block16 : 0≤(C16.map rawR).prod ∧ (C16.map rawR).prod≤((249997430381/250000000000:ℚ):ℝ) := by
  have hQ : 0≤(C16.map rawQ).prod ∧ (C16.map rawQ).prod≤(249997430381/250000000000:ℚ) := by
    norm_num [C16,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C16.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C16.map rawQ).prod:ℚ):ℝ)≤((249997430381/250000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C17 : List ℕ :=[1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087]
theorem prime17 : ∀ p∈C17, p.Prime := by
  simp only [C17,List.forall_mem_cons]
  norm_num
theorem block17 : 0≤(C17.map rawR).prod ∧ (C17.map rawR).prod≤((31249715951/31250000000:ℚ):ℝ) := by
  have hQ : 0≤(C17.map rawQ).prod ∧ (C17.map rawQ).prod≤(31249715951/31250000000:ℚ) := by
    norm_num [C17,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C17.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C17.map rawQ).prod:ℚ):ℝ)≤((31249715951/31250000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C18 : List ℕ :=[1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153]
theorem prime18 : ∀ p∈C18, p.Prime := by
  simp only [C18,List.forall_mem_cons]
  norm_num
theorem block18 : 0≤(C18.map rawR).prod ∧ (C18.map rawR).prod≤((124998994549/125000000000:ℚ):ℝ) := by
  have hQ : 0≤(C18.map rawQ).prod ∧ (C18.map rawQ).prod≤(124998994549/125000000000:ℚ) := by
    norm_num [C18,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C18.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C18.map rawQ).prod:ℚ):ℝ)≤((124998994549/125000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C19 : List ℕ :=[1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229]
theorem prime19 : ∀ p∈C19, p.Prime := by
  simp only [C19,List.forall_mem_cons]
  norm_num
theorem block19 : 0≤(C19.map rawR).prod ∧ (C19.map rawR).prod≤((999993011687/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C19.map rawQ).prod ∧ (C19.map rawQ).prod≤(999993011687/1000000000000:ℚ) := by
    norm_num [C19,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C19.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C19.map rawQ).prod:ℚ):ℝ)≤((999993011687/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C20 : List ℕ :=[1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297]
theorem prime20 : ∀ p∈C20, p.Prime := by
  simp only [C20,List.forall_mem_cons]
  norm_num
theorem block20 : 0≤(C20.map rawR).prod ∧ (C20.map rawR).prod≤((999993776527/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C20.map rawQ).prod ∧ (C20.map rawQ).prod≤(999993776527/1000000000000:ℚ) := by
    norm_num [C20,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C20.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C20.map rawQ).prod:ℚ):ℝ)≤((999993776527/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C21 : List ℕ :=[1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381]
theorem prime21 : ∀ p∈C21, p.Prime := by
  simp only [C21,List.forall_mem_cons]
  norm_num
theorem block21 : 0≤(C21.map rawR).prod ∧ (C21.map rawR).prod≤((999994380867/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C21.map rawQ).prod ∧ (C21.map rawQ).prod≤(999994380867/1000000000000:ℚ) := by
    norm_num [C21,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C21.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C21.map rawQ).prod:ℚ):ℝ)≤((999994380867/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C22 : List ℕ :=[1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453]
theorem prime22 : ∀ p∈C22, p.Prime := by
  simp only [C22,List.forall_mem_cons]
  norm_num
theorem block22 : 0≤(C22.map rawR).prod ∧ (C22.map rawR).prod≤((999995107773/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C22.map rawQ).prod ∧ (C22.map rawQ).prod≤(999995107773/1000000000000:ℚ) := by
    norm_num [C22,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C22.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C22.map rawQ).prod:ℚ):ℝ)≤((999995107773/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C23 : List ℕ :=[1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523]
theorem prime23 : ∀ p∈C23, p.Prime := by
  simp only [C23,List.forall_mem_cons]
  norm_num
theorem block23 : 0≤(C23.map rawR).prod ∧ (C23.map rawR).prod≤((199999097071/200000000000:ℚ):ℝ) := by
  have hQ : 0≤(C23.map rawQ).prod ∧ (C23.map rawQ).prod≤(199999097071/200000000000:ℚ) := by
    norm_num [C23,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C23.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C23.map rawQ).prod:ℚ):ℝ)≤((199999097071/200000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C24 : List ℕ :=[1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597]
theorem prime24 : ∀ p∈C24, p.Prime := by
  simp only [C24,List.forall_mem_cons]
  norm_num
theorem block24 : 0≤(C24.map rawR).prod ∧ (C24.map rawR).prod≤((999995900609/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C24.map rawQ).prod ∧ (C24.map rawQ).prod≤(999995900609/1000000000000:ℚ) := by
    norm_num [C24,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C24.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C24.map rawQ).prod:ℚ):ℝ)≤((999995900609/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C25 : List ℕ :=[1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663]
theorem prime25 : ∀ p∈C25, p.Prime := by
  simp only [C25,List.forall_mem_cons]
  norm_num
theorem block25 : 0≤(C25.map rawR).prod ∧ (C25.map rawR).prod≤((999996208537/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C25.map rawQ).prod ∧ (C25.map rawQ).prod≤(999996208537/1000000000000:ℚ) := by
    norm_num [C25,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C25.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C25.map rawQ).prod:ℚ):ℝ)≤((999996208537/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C26 : List ℕ :=[1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741]
theorem prime26 : ∀ p∈C26, p.Prime := by
  simp only [C26,List.forall_mem_cons]
  norm_num
theorem block26 : 0≤(C26.map rawR).prod ∧ (C26.map rawR).prod≤((99999655481/100000000000:ℚ):ℝ) := by
  have hQ : 0≤(C26.map rawQ).prod ∧ (C26.map rawQ).prod≤(99999655481/100000000000:ℚ) := by
    norm_num [C26,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C26.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C26.map rawQ).prod:ℚ):ℝ)≤((99999655481/100000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C27 : List ℕ :=[1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823]
theorem prime27 : ∀ p∈C27, p.Prime := by
  simp only [C27,List.forall_mem_cons]
  norm_num
theorem block27 : 0≤(C27.map rawR).prod ∧ (C27.map rawR).prod≤((499998424631/500000000000:ℚ):ℝ) := by
  have hQ : 0≤(C27.map rawQ).prod ∧ (C27.map rawQ).prod≤(499998424631/500000000000:ℚ) := by
    norm_num [C27,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C27.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C27.map rawQ).prod:ℚ):ℝ)≤((499998424631/500000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C28 : List ℕ :=[1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901]
theorem prime28 : ∀ p∈C28, p.Prime := by
  simp only [C28,List.forall_mem_cons]
  norm_num
theorem block28 : 0≤(C28.map rawR).prod ∧ (C28.map rawR).prod≤((19999942703/20000000000:ℚ):ℝ) := by
  have hQ : 0≤(C28.map rawQ).prod ∧ (C28.map rawQ).prod≤(19999942703/20000000000:ℚ) := by
    norm_num [C28,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C28.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C28.map rawQ).prod:ℚ):ℝ)≤((19999942703/20000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C29 : List ℕ :=[1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993]
theorem prime29 : ∀ p∈C29, p.Prime := by
  simp only [C29,List.forall_mem_cons]
  norm_num
theorem block29 : 0≤(C29.map rawR).prod ∧ (C29.map rawR).prod≤((499998685011/500000000000:ℚ):ℝ) := by
  have hQ : 0≤(C29.map rawQ).prod ∧ (C29.map rawQ).prod≤(499998685011/500000000000:ℚ) := by
    norm_num [C29,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C29.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C29.map rawQ).prod:ℚ):ℝ)≤((499998685011/500000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def C30 : List ℕ :=[1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039]
theorem prime30 : ∀ p∈C30, p.Prime := by
  simp only [C30,List.forall_mem_cons]
  norm_num
theorem block30 : 0≤(C30.map rawR).prod ∧ (C30.map rawR).prod≤((999998027899/1000000000000:ℚ):ℝ) := by
  have hQ : 0≤(C30.map rawQ).prod ∧ (C30.map rawQ).prod≤(999998027899/1000000000000:ℚ) := by
    norm_num [C30,rawQ]
  constructor
  · have hr : (0:ℝ)≤(((C30.map rawQ).prod:ℚ):ℝ) := by exact_mod_cast hQ.1
    rwa [cast_raw_prod] at hr
  · have hr : (((C30.map rawQ).prod:ℚ):ℝ)≤((999998027899/1000000000000:ℚ):ℝ) := Rat.cast_le.mpr hQ.2
    rwa [cast_raw_prod] at hr

end TwinUpperShort
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace TwinUpperShort
def PL : List ℕ :=C0 ++ C1 ++ C2 ++ C3 ++ C4 ++ C5 ++ C6 ++ C7 ++ C8 ++ C9 ++ C10 ++ C11 ++ C12 ++ C13 ++ C14 ++ C15 ++ C16 ++ C17 ++ C18 ++ C19 ++ C20 ++ C21 ++ C22 ++ C23 ++ C24 ++ C25 ++ C26 ++ C27 ++ C28 ++ C29 ++ C30
theorem PL_prime : ∀ p∈PL, p.Prime := List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨prime0,prime1⟩,prime2⟩,prime3⟩,prime4⟩,prime5⟩,prime6⟩,prime7⟩,prime8⟩,prime9⟩,prime10⟩,prime11⟩,prime12⟩,prime13⟩,prime14⟩,prime15⟩,prime16⟩,prime17⟩,prime18⟩,prime19⟩,prime20⟩,prime21⟩,prime22⟩,prime23⟩,prime24⟩,prime25⟩,prime26⟩,prime27⟩,prime28⟩,prime29⟩,prime30⟩
theorem PL_bounds : ∀ p∈PL, 2<p ∧ p<2048 := by decide +kernel
theorem PL_nodup : PL.Nodup := by
  have hh : List.IsChain (·<·) PL := by decide +kernel
  exact (List.sortedLT_iff_isChain.mpr hh).nodup
def QS : Finset ℕ :=⟨(PL:Multiset ℕ),Multiset.coe_nodup.mpr PL_nodup⟩
lemma prod_QS (f : ℕ→ℝ) : (∏ p∈QS, f p)=(PL.map f).prod := by
  show Multiset.prod (Multiset.map f (PL:Multiset ℕ))=_
  rw [Multiset.map_coe,Multiset.prod_coe]
attribute [local irreducible] rawR PL C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30
lemma prefix_00 : (C0.map rawR).prod≤((166099838443/250000000000:ℚ):ℝ) := by
  exact block0.2
lemma prefix_01 : (C0.map rawR).prod * (C1.map rawR).prod≤((66174144791/100000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_00 block1.2 block1.1
    (by norm_num : (0:ℝ)≤((166099838443/250000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_02 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod≤((20657421921/31250000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_01 block2.2 block2.1
    (by norm_num : (0:ℝ)≤((66174144791/100000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_03 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod≤((132149777323/200000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_02 block3.2 block3.1
    (by norm_num : (0:ℝ)≤((20657421921/31250000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_04 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod≤((330295957707/500000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_03 block4.2 block4.1
    (by norm_num : (0:ℝ)≤((132149777323/200000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_05 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod≤((82561856831/125000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_04 block5.2 block5.1
    (by norm_num : (0:ℝ)≤((330295957707/500000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_06 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod≤((660431566969/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_05 block6.2 block6.1
    (by norm_num : (0:ℝ)≤((82561856831/125000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_07 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod≤((82548386397/125000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_06 block7.2 block7.1
    (by norm_num : (0:ℝ)≤((660431566969/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_08 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod≤((660353693233/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_07 block8.2 block8.1
    (by norm_num : (0:ℝ)≤((82548386397/125000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_09 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod≤((330164035091/500000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_08 block9.2 block9.1
    (by norm_num : (0:ℝ)≤((660353693233/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_10 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod≤((660308488323/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_09 block10.2 block10.1
    (by norm_num : (0:ℝ)≤((330164035091/500000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_11 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod≤((82536525273/125000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_10 block11.2 block11.1
    (by norm_num : (0:ℝ)≤((660308488323/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_12 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod≤((165069711439/250000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_11 block12.2 block12.1
    (by norm_num : (0:ℝ)≤((82536525273/125000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_13 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod≤((330133909209/500000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_12 block13.2 block13.1
    (by norm_num : (0:ℝ)≤((165069711439/250000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_14 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod≤((66025853169/100000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_13 block14.2 block14.1
    (by norm_num : (0:ℝ)≤((330133909209/500000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_15 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod≤((660250598763/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_14 block15.2 block15.1
    (by norm_num : (0:ℝ)≤((66025853169/100000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_16 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod≤((330121906197/500000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_15 block16.2 block16.1
    (by norm_num : (0:ℝ)≤((660250598763/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_17 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod≤((660237811063/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_16 block17.2 block17.1
    (by norm_num : (0:ℝ)≤((330121906197/500000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_18 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod≤((660232500369/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_17 block18.2 block18.1
    (by norm_num : (0:ℝ)≤((660237811063/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_19 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod≤((330113943229/500000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_18 block19.2 block19.1
    (by norm_num : (0:ℝ)≤((660232500369/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_20 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod≤((165055944387/250000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_19 block20.2 block20.1
    (by norm_num : (0:ℝ)≤((330113943229/500000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_21 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod≤((660220067663/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_20 block21.2 block21.1
    (by norm_num : (0:ℝ)≤((165055944387/250000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_22 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod≤((660216837717/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_21 block22.2 block22.1
    (by norm_num : (0:ℝ)≤((660220067663/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_23 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod≤((660213857073/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_22 block23.2 block23.1
    (by norm_num : (0:ℝ)≤((660216837717/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_24 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod≤((660211150599/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_23 block24.2 block24.1
    (by norm_num : (0:ℝ)≤((660213857073/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_25 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod * (C25.map rawR).prod≤((660208647433/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_24 block25.2 block25.1
    (by norm_num : (0:ℝ)≤((660211150599/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_26 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod * (C25.map rawR).prod * (C26.map rawR).prod≤((660206372889/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_25 block26.2 block26.1
    (by norm_num : (0:ℝ)≤((660208647433/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_27 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod * (C25.map rawR).prod * (C26.map rawR).prod * (C27.map rawR).prod≤((41262768297/62500000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_26 block27.2 block27.1
    (by norm_num : (0:ℝ)≤((660206372889/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_28 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod * (C25.map rawR).prod * (C26.map rawR).prod * (C27.map rawR).prod * (C28.map rawR).prod≤((330101200683/500000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_27 block28.2 block28.1
    (by norm_num : (0:ℝ)≤((41262768297/62500000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_29 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod * (C25.map rawR).prod * (C26.map rawR).prod * (C27.map rawR).prod * (C28.map rawR).prod * (C29.map rawR).prod≤((660200665049/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_28 block29.2 block29.1
    (by norm_num : (0:ℝ)≤((330101200683/500000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma prefix_30 : (C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod * (C25.map rawR).prod * (C26.map rawR).prod * (C27.map rawR).prod * (C28.map rawR).prod * (C29.map rawR).prod * (C30.map rawR).prod≤((660199363067/1000000000000:ℚ):ℝ) := by
  have hh := mul_le_mul prefix_29 block30.2 block30.1
    (by norm_num : (0:ℝ)≤((660200665049/1000000000000:ℚ):ℝ))
  exact hh.trans (by norm_num)
lemma product_chunks (f : ℕ→ℝ) (L0 : List ℕ) (L1 : List ℕ) (L2 : List ℕ) (L3 : List ℕ) (L4 : List ℕ) (L5 : List ℕ) (L6 : List ℕ) (L7 : List ℕ) (L8 : List ℕ) (L9 : List ℕ) (L10 : List ℕ) (L11 : List ℕ) (L12 : List ℕ) (L13 : List ℕ) (L14 : List ℕ) (L15 : List ℕ) (L16 : List ℕ) (L17 : List ℕ) (L18 : List ℕ) (L19 : List ℕ) (L20 : List ℕ) (L21 : List ℕ) (L22 : List ℕ) (L23 : List ℕ) (L24 : List ℕ) (L25 : List ℕ) (L26 : List ℕ) (L27 : List ℕ) (L28 : List ℕ) (L29 : List ℕ) (L30 : List ℕ) :
    ((L0 ++ L1 ++ L2 ++ L3 ++ L4 ++ L5 ++ L6 ++ L7 ++ L8 ++ L9 ++ L10 ++ L11 ++ L12 ++ L13 ++ L14 ++ L15 ++ L16 ++ L17 ++ L18 ++ L19 ++ L20 ++ L21 ++ L22 ++ L23 ++ L24 ++ L25 ++ L26 ++ L27 ++ L28 ++ L29 ++ L30).map f).prod=(L0.map f).prod * (L1.map f).prod * (L2.map f).prod * (L3.map f).prod * (L4.map f).prod * (L5.map f).prod * (L6.map f).prod * (L7.map f).prod * (L8.map f).prod * (L9.map f).prod * (L10.map f).prod * (L11.map f).prod * (L12.map f).prod * (L13.map f).prod * (L14.map f).prod * (L15.map f).prod * (L16.map f).prod * (L17.map f).prod * (L18.map f).prod * (L19.map f).prod * (L20.map f).prod * (L21.map f).prod * (L22.map f).prod * (L23.map f).prod * (L24.map f).prod * (L25.map f).prod * (L26.map f).prod * (L27.map f).prod * (L28.map f).prod * (L29.map f).prod * (L30.map f).prod := by
  simp only [List.map_append,List.prod_append,mul_assoc]
lemma partial_raw_upper : TaoFivePrimes.twinPrimePartial 2047≤(PL.map rawR).prod := by
  have hsub : QS⊆Finset.range 2048 := by
    intro p hp
    have hpl : p∈PL := by simpa [QS] using hp
    exact Finset.mem_range.mpr (PL_bounds p hpl).2
  have hle : TaoFivePrimes.twinPrimePartial 2047≤
      ∏ p∈QS, (if p.Prime ∧ 2<p then 1-1/((p:ℝ)-1)^2 else 1) := by
    unfold TaoFivePrimes.twinPrimePartial
    apply Finset.prod_le_prod_of_subset_of_le_one hsub
    · intro p hp
      exact twinPartial_fac_nonneg p
    · intro p hp hnot
      exact twinPartial_fac_le_one p
  have he : (∏ p∈QS, (if p.Prime ∧ 2<p then 1-1/((p:ℝ)-1)^2 else 1))=
      (PL.map rawR).prod := by
    rw [←prod_QS]
    apply Finset.prod_congr rfl
    intro p hp
    have hpl : p∈PL := by simpa [QS] using hp
    rw [if_pos ⟨PL_prime p hpl,(PL_bounds p hpl).1⟩]
    rw [rawR]
  rw [he] at hle
  exact hle
lemma partial_upper : TaoFivePrimes.twinPrimePartial 2047≤(0.6602:ℝ) := by
  calc
    _ ≤(PL.map rawR).prod := partial_raw_upper
    _ =(C0.map rawR).prod * (C1.map rawR).prod * (C2.map rawR).prod * (C3.map rawR).prod * (C4.map rawR).prod * (C5.map rawR).prod * (C6.map rawR).prod * (C7.map rawR).prod * (C8.map rawR).prod * (C9.map rawR).prod * (C10.map rawR).prod * (C11.map rawR).prod * (C12.map rawR).prod * (C13.map rawR).prod * (C14.map rawR).prod * (C15.map rawR).prod * (C16.map rawR).prod * (C17.map rawR).prod * (C18.map rawR).prod * (C19.map rawR).prod * (C20.map rawR).prod * (C21.map rawR).prod * (C22.map rawR).prod * (C23.map rawR).prod * (C24.map rawR).prod * (C25.map rawR).prod * (C26.map rawR).prod * (C27.map rawR).prod * (C28.map rawR).prod * (C29.map rawR).prod * (C30.map rawR).prod := by
      unfold PL
      exact product_chunks rawR C0 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28 C29 C30
    _ ≤((660199363067/1000000000000:ℚ):ℝ) := prefix_30
    _ ≤_ := by norm_num
end TwinUpperShort
theorem solution :
    TaoFivePrimes.twinPrimeConstant≤(1.3204:ℝ) := by
  unfold TaoFivePrimes.twinPrimeConstant
  have hbdd : BddBelow (Set.range TaoFivePrimes.twinPrimePartial) :=
    ⟨0,by rintro _ ⟨Q,rfl⟩; exact TwinUpperShort.twinPartial_nonneg Q⟩
  have hi : sInf (Set.range TaoFivePrimes.twinPrimePartial)≤
      TaoFivePrimes.twinPrimePartial 2047 :=csInf_le hbdd ⟨2047,rfl⟩
  linarith [hi,TwinUpperShort.partial_upper]
#print axioms solution
