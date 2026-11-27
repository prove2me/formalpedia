-- Prove2me | solution 1 for TargetedSamplers.Structured.Interp.call_exec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:20:45.154812+00:00
-- url     : https://prove2.me/submissions/b283b8d3-106e-45d0-b4e4-5b88ea33347f

import Definitions.Def_LogCostRAM_Interpreter

-- ===== Solutions/Dev/InterpA.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

theorem size_add_le (a b : ℕ) : (a+b).size ≤ a.size + b.size + 1 := by
  rw [Nat.size_le]
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2^a.size ≤ 2^(a.size+b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2^b.size ≤ 2^(a.size+b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

theorem size_mono {a b : ℕ} (h : a ≤ b) : a.size ≤ b.size := Nat.size_le_size h

theorem size_le_of_lt4 {a : ℕ} (h : a < 4) : a.size ≤ 2 := by
  rw [Nat.size_le]; simpa using h

theorem bitVal_size (o : Option Bool) : (bitVal o).size ≤ 2 := by
  apply size_le_of_lt4; cases o with
  | none => simp [bitVal]
  | some b => cases b <;> simp [bitVal]

theorem toNat_size (b : Bool) : b.toNat.size ≤ 2 := by
  apply size_le_of_lt4; cases b <;> simp

@[simp] theorem write_mem_self (S : Store) (d v : ℕ) : (S.write d v).mem d = v := by
  simp [Store.write]

theorem write_mem_ne (S : Store) {d y : ℕ} (v : ℕ) (h : y ≠ d) : (S.write d v).mem y = S.mem y := by
  simp [Store.write, h]

@[simp] theorem write_out (S : Store) (d v : ℕ) : (S.write d v).out = S.out := rfl

theorem write_mem (S : Store) (d v y : ℕ) :
    (S.write d v).mem y = if y = d then v else S.mem y := by
  simp [Store.write, Function.update_apply]

structure Lay (r : IRegs) (B L XB K J W : ℕ) : Prop where
  lt : ∀ y ∈ r.all, y < XB
  nz : ∀ y ∈ r.all, y ≠ 0
  sz : ∀ y ∈ r.all, y.size ≤ K
  xl : XB ≤ L
  lb : L < B
  wb : B.size + J + 1 ≤ W
  k1 : 1 ≤ K

structure Dist (r : IRegs) : Prop where
  pc_run : r.pc ≠ r.run
  pc_big : r.pc ≠ r.big
  pc_logb : r.pc ≠ r.logb
  pc_cnt : r.pc ≠ r.cnt
  pc_xb : r.pc ≠ r.xb
  pc_xlen : r.pc ≠ r.xlen
  pc_co : r.pc ≠ r.co
  pc_cl : r.pc ≠ r.cl
  pc_cap : r.pc ≠ r.cap
  pc_one : r.pc ≠ r.one
  pc_zero : r.pc ≠ r.zero
  pc_ds : r.pc ≠ r.ds
  pc_t1 : r.pc ≠ r.t1
  pc_t2 : r.pc ≠ r.t2
  pc_t3 : r.pc ≠ r.t3
  pc_t4 : r.pc ≠ r.t4
  pc_t5 : r.pc ≠ r.t5
  pc_t6 : r.pc ≠ r.t6
  run_pc : r.run ≠ r.pc
  run_big : r.run ≠ r.big
  run_logb : r.run ≠ r.logb
  run_cnt : r.run ≠ r.cnt
  run_xb : r.run ≠ r.xb
  run_xlen : r.run ≠ r.xlen
  run_co : r.run ≠ r.co
  run_cl : r.run ≠ r.cl
  run_cap : r.run ≠ r.cap
  run_one : r.run ≠ r.one
  run_zero : r.run ≠ r.zero
  run_ds : r.run ≠ r.ds
  run_t1 : r.run ≠ r.t1
  run_t2 : r.run ≠ r.t2
  run_t3 : r.run ≠ r.t3
  run_t4 : r.run ≠ r.t4
  run_t5 : r.run ≠ r.t5
  run_t6 : r.run ≠ r.t6
  big_pc : r.big ≠ r.pc
  big_run : r.big ≠ r.run
  big_logb : r.big ≠ r.logb
  big_cnt : r.big ≠ r.cnt
  big_xb : r.big ≠ r.xb
  big_xlen : r.big ≠ r.xlen
  big_co : r.big ≠ r.co
  big_cl : r.big ≠ r.cl
  big_cap : r.big ≠ r.cap
  big_one : r.big ≠ r.one
  big_zero : r.big ≠ r.zero
  big_ds : r.big ≠ r.ds
  big_t1 : r.big ≠ r.t1
  big_t2 : r.big ≠ r.t2
  big_t3 : r.big ≠ r.t3
  big_t4 : r.big ≠ r.t4
  big_t5 : r.big ≠ r.t5
  big_t6 : r.big ≠ r.t6
  logb_pc : r.logb ≠ r.pc
  logb_run : r.logb ≠ r.run
  logb_big : r.logb ≠ r.big
  logb_cnt : r.logb ≠ r.cnt
  logb_xb : r.logb ≠ r.xb
  logb_xlen : r.logb ≠ r.xlen
  logb_co : r.logb ≠ r.co
  logb_cl : r.logb ≠ r.cl
  logb_cap : r.logb ≠ r.cap
  logb_one : r.logb ≠ r.one
  logb_zero : r.logb ≠ r.zero
  logb_ds : r.logb ≠ r.ds
  logb_t1 : r.logb ≠ r.t1
  logb_t2 : r.logb ≠ r.t2
  logb_t3 : r.logb ≠ r.t3
  logb_t4 : r.logb ≠ r.t4
  logb_t5 : r.logb ≠ r.t5
  logb_t6 : r.logb ≠ r.t6
  cnt_pc : r.cnt ≠ r.pc
  cnt_run : r.cnt ≠ r.run
  cnt_big : r.cnt ≠ r.big
  cnt_logb : r.cnt ≠ r.logb
  cnt_xb : r.cnt ≠ r.xb
  cnt_xlen : r.cnt ≠ r.xlen
  cnt_co : r.cnt ≠ r.co
  cnt_cl : r.cnt ≠ r.cl
  cnt_cap : r.cnt ≠ r.cap
  cnt_one : r.cnt ≠ r.one
  cnt_zero : r.cnt ≠ r.zero
  cnt_ds : r.cnt ≠ r.ds
  cnt_t1 : r.cnt ≠ r.t1
  cnt_t2 : r.cnt ≠ r.t2
  cnt_t3 : r.cnt ≠ r.t3
  cnt_t4 : r.cnt ≠ r.t4
  cnt_t5 : r.cnt ≠ r.t5
  cnt_t6 : r.cnt ≠ r.t6
  xb_pc : r.xb ≠ r.pc
  xb_run : r.xb ≠ r.run
  xb_big : r.xb ≠ r.big
  xb_logb : r.xb ≠ r.logb
  xb_cnt : r.xb ≠ r.cnt
  xb_xlen : r.xb ≠ r.xlen
  xb_co : r.xb ≠ r.co
  xb_cl : r.xb ≠ r.cl
  xb_cap : r.xb ≠ r.cap
  xb_one : r.xb ≠ r.one
  xb_zero : r.xb ≠ r.zero
  xb_ds : r.xb ≠ r.ds
  xb_t1 : r.xb ≠ r.t1
  xb_t2 : r.xb ≠ r.t2
  xb_t3 : r.xb ≠ r.t3
  xb_t4 : r.xb ≠ r.t4
  xb_t5 : r.xb ≠ r.t5
  xb_t6 : r.xb ≠ r.t6
  xlen_pc : r.xlen ≠ r.pc
  xlen_run : r.xlen ≠ r.run
  xlen_big : r.xlen ≠ r.big
  xlen_logb : r.xlen ≠ r.logb
  xlen_cnt : r.xlen ≠ r.cnt
  xlen_xb : r.xlen ≠ r.xb
  xlen_co : r.xlen ≠ r.co
  xlen_cl : r.xlen ≠ r.cl
  xlen_cap : r.xlen ≠ r.cap
  xlen_one : r.xlen ≠ r.one
  xlen_zero : r.xlen ≠ r.zero
  xlen_ds : r.xlen ≠ r.ds
  xlen_t1 : r.xlen ≠ r.t1
  xlen_t2 : r.xlen ≠ r.t2
  xlen_t3 : r.xlen ≠ r.t3
  xlen_t4 : r.xlen ≠ r.t4
  xlen_t5 : r.xlen ≠ r.t5
  xlen_t6 : r.xlen ≠ r.t6
  co_pc : r.co ≠ r.pc
  co_run : r.co ≠ r.run
  co_big : r.co ≠ r.big
  co_logb : r.co ≠ r.logb
  co_cnt : r.co ≠ r.cnt
  co_xb : r.co ≠ r.xb
  co_xlen : r.co ≠ r.xlen
  co_cl : r.co ≠ r.cl
  co_cap : r.co ≠ r.cap
  co_one : r.co ≠ r.one
  co_zero : r.co ≠ r.zero
  co_ds : r.co ≠ r.ds
  co_t1 : r.co ≠ r.t1
  co_t2 : r.co ≠ r.t2
  co_t3 : r.co ≠ r.t3
  co_t4 : r.co ≠ r.t4
  co_t5 : r.co ≠ r.t5
  co_t6 : r.co ≠ r.t6
  cl_pc : r.cl ≠ r.pc
  cl_run : r.cl ≠ r.run
  cl_big : r.cl ≠ r.big
  cl_logb : r.cl ≠ r.logb
  cl_cnt : r.cl ≠ r.cnt
  cl_xb : r.cl ≠ r.xb
  cl_xlen : r.cl ≠ r.xlen
  cl_co : r.cl ≠ r.co
  cl_cap : r.cl ≠ r.cap
  cl_one : r.cl ≠ r.one
  cl_zero : r.cl ≠ r.zero
  cl_ds : r.cl ≠ r.ds
  cl_t1 : r.cl ≠ r.t1
  cl_t2 : r.cl ≠ r.t2
  cl_t3 : r.cl ≠ r.t3
  cl_t4 : r.cl ≠ r.t4
  cl_t5 : r.cl ≠ r.t5
  cl_t6 : r.cl ≠ r.t6
  cap_pc : r.cap ≠ r.pc
  cap_run : r.cap ≠ r.run
  cap_big : r.cap ≠ r.big
  cap_logb : r.cap ≠ r.logb
  cap_cnt : r.cap ≠ r.cnt
  cap_xb : r.cap ≠ r.xb
  cap_xlen : r.cap ≠ r.xlen
  cap_co : r.cap ≠ r.co
  cap_cl : r.cap ≠ r.cl
  cap_one : r.cap ≠ r.one
  cap_zero : r.cap ≠ r.zero
  cap_ds : r.cap ≠ r.ds
  cap_t1 : r.cap ≠ r.t1
  cap_t2 : r.cap ≠ r.t2
  cap_t3 : r.cap ≠ r.t3
  cap_t4 : r.cap ≠ r.t4
  cap_t5 : r.cap ≠ r.t5
  cap_t6 : r.cap ≠ r.t6
  one_pc : r.one ≠ r.pc
  one_run : r.one ≠ r.run
  one_big : r.one ≠ r.big
  one_logb : r.one ≠ r.logb
  one_cnt : r.one ≠ r.cnt
  one_xb : r.one ≠ r.xb
  one_xlen : r.one ≠ r.xlen
  one_co : r.one ≠ r.co
  one_cl : r.one ≠ r.cl
  one_cap : r.one ≠ r.cap
  one_zero : r.one ≠ r.zero
  one_ds : r.one ≠ r.ds
  one_t1 : r.one ≠ r.t1
  one_t2 : r.one ≠ r.t2
  one_t3 : r.one ≠ r.t3
  one_t4 : r.one ≠ r.t4
  one_t5 : r.one ≠ r.t5
  one_t6 : r.one ≠ r.t6
  zero_pc : r.zero ≠ r.pc
  zero_run : r.zero ≠ r.run
  zero_big : r.zero ≠ r.big
  zero_logb : r.zero ≠ r.logb
  zero_cnt : r.zero ≠ r.cnt
  zero_xb : r.zero ≠ r.xb
  zero_xlen : r.zero ≠ r.xlen
  zero_co : r.zero ≠ r.co
  zero_cl : r.zero ≠ r.cl
  zero_cap : r.zero ≠ r.cap
  zero_one : r.zero ≠ r.one
  zero_ds : r.zero ≠ r.ds
  zero_t1 : r.zero ≠ r.t1
  zero_t2 : r.zero ≠ r.t2
  zero_t3 : r.zero ≠ r.t3
  zero_t4 : r.zero ≠ r.t4
  zero_t5 : r.zero ≠ r.t5
  zero_t6 : r.zero ≠ r.t6
  ds_pc : r.ds ≠ r.pc
  ds_run : r.ds ≠ r.run
  ds_big : r.ds ≠ r.big
  ds_logb : r.ds ≠ r.logb
  ds_cnt : r.ds ≠ r.cnt
  ds_xb : r.ds ≠ r.xb
  ds_xlen : r.ds ≠ r.xlen
  ds_co : r.ds ≠ r.co
  ds_cl : r.ds ≠ r.cl
  ds_cap : r.ds ≠ r.cap
  ds_one : r.ds ≠ r.one
  ds_zero : r.ds ≠ r.zero
  ds_t1 : r.ds ≠ r.t1
  ds_t2 : r.ds ≠ r.t2
  ds_t3 : r.ds ≠ r.t3
  ds_t4 : r.ds ≠ r.t4
  ds_t5 : r.ds ≠ r.t5
  ds_t6 : r.ds ≠ r.t6
  t1_pc : r.t1 ≠ r.pc
  t1_run : r.t1 ≠ r.run
  t1_big : r.t1 ≠ r.big
  t1_logb : r.t1 ≠ r.logb
  t1_cnt : r.t1 ≠ r.cnt
  t1_xb : r.t1 ≠ r.xb
  t1_xlen : r.t1 ≠ r.xlen
  t1_co : r.t1 ≠ r.co
  t1_cl : r.t1 ≠ r.cl
  t1_cap : r.t1 ≠ r.cap
  t1_one : r.t1 ≠ r.one
  t1_zero : r.t1 ≠ r.zero
  t1_ds : r.t1 ≠ r.ds
  t1_t2 : r.t1 ≠ r.t2
  t1_t3 : r.t1 ≠ r.t3
  t1_t4 : r.t1 ≠ r.t4
  t1_t5 : r.t1 ≠ r.t5
  t1_t6 : r.t1 ≠ r.t6
  t2_pc : r.t2 ≠ r.pc
  t2_run : r.t2 ≠ r.run
  t2_big : r.t2 ≠ r.big
  t2_logb : r.t2 ≠ r.logb
  t2_cnt : r.t2 ≠ r.cnt
  t2_xb : r.t2 ≠ r.xb
  t2_xlen : r.t2 ≠ r.xlen
  t2_co : r.t2 ≠ r.co
  t2_cl : r.t2 ≠ r.cl
  t2_cap : r.t2 ≠ r.cap
  t2_one : r.t2 ≠ r.one
  t2_zero : r.t2 ≠ r.zero
  t2_ds : r.t2 ≠ r.ds
  t2_t1 : r.t2 ≠ r.t1
  t2_t3 : r.t2 ≠ r.t3
  t2_t4 : r.t2 ≠ r.t4
  t2_t5 : r.t2 ≠ r.t5
  t2_t6 : r.t2 ≠ r.t6
  t3_pc : r.t3 ≠ r.pc
  t3_run : r.t3 ≠ r.run
  t3_big : r.t3 ≠ r.big
  t3_logb : r.t3 ≠ r.logb
  t3_cnt : r.t3 ≠ r.cnt
  t3_xb : r.t3 ≠ r.xb
  t3_xlen : r.t3 ≠ r.xlen
  t3_co : r.t3 ≠ r.co
  t3_cl : r.t3 ≠ r.cl
  t3_cap : r.t3 ≠ r.cap
  t3_one : r.t3 ≠ r.one
  t3_zero : r.t3 ≠ r.zero
  t3_ds : r.t3 ≠ r.ds
  t3_t1 : r.t3 ≠ r.t1
  t3_t2 : r.t3 ≠ r.t2
  t3_t4 : r.t3 ≠ r.t4
  t3_t5 : r.t3 ≠ r.t5
  t3_t6 : r.t3 ≠ r.t6
  t4_pc : r.t4 ≠ r.pc
  t4_run : r.t4 ≠ r.run
  t4_big : r.t4 ≠ r.big
  t4_logb : r.t4 ≠ r.logb
  t4_cnt : r.t4 ≠ r.cnt
  t4_xb : r.t4 ≠ r.xb
  t4_xlen : r.t4 ≠ r.xlen
  t4_co : r.t4 ≠ r.co
  t4_cl : r.t4 ≠ r.cl
  t4_cap : r.t4 ≠ r.cap
  t4_one : r.t4 ≠ r.one
  t4_zero : r.t4 ≠ r.zero
  t4_ds : r.t4 ≠ r.ds
  t4_t1 : r.t4 ≠ r.t1
  t4_t2 : r.t4 ≠ r.t2
  t4_t3 : r.t4 ≠ r.t3
  t4_t5 : r.t4 ≠ r.t5
  t4_t6 : r.t4 ≠ r.t6
  t5_pc : r.t5 ≠ r.pc
  t5_run : r.t5 ≠ r.run
  t5_big : r.t5 ≠ r.big
  t5_logb : r.t5 ≠ r.logb
  t5_cnt : r.t5 ≠ r.cnt
  t5_xb : r.t5 ≠ r.xb
  t5_xlen : r.t5 ≠ r.xlen
  t5_co : r.t5 ≠ r.co
  t5_cl : r.t5 ≠ r.cl
  t5_cap : r.t5 ≠ r.cap
  t5_one : r.t5 ≠ r.one
  t5_zero : r.t5 ≠ r.zero
  t5_ds : r.t5 ≠ r.ds
  t5_t1 : r.t5 ≠ r.t1
  t5_t2 : r.t5 ≠ r.t2
  t5_t3 : r.t5 ≠ r.t3
  t5_t4 : r.t5 ≠ r.t4
  t5_t6 : r.t5 ≠ r.t6
  t6_pc : r.t6 ≠ r.pc
  t6_run : r.t6 ≠ r.run
  t6_big : r.t6 ≠ r.big
  t6_logb : r.t6 ≠ r.logb
  t6_cnt : r.t6 ≠ r.cnt
  t6_xb : r.t6 ≠ r.xb
  t6_xlen : r.t6 ≠ r.xlen
  t6_co : r.t6 ≠ r.co
  t6_cl : r.t6 ≠ r.cl
  t6_cap : r.t6 ≠ r.cap
  t6_one : r.t6 ≠ r.one
  t6_zero : r.t6 ≠ r.zero
  t6_ds : r.t6 ≠ r.ds
  t6_t1 : r.t6 ≠ r.t1
  t6_t2 : r.t6 ≠ r.t2
  t6_t3 : r.t6 ≠ r.t3
  t6_t4 : r.t6 ≠ r.t4
  t6_t5 : r.t6 ≠ r.t5

theorem Dist.of {r : IRegs} (h : r.all.Nodup) : Dist r :=
  have H0 := List.pairwise_iff_getElem.1 h
  have H : ∀ i j (hi : i < 19) (hj : j < 19), i < j → r.all[i]'hi ≠ r.all[j]'hj :=
    fun i j hi hj hij => H0 i j hi hj hij
  {
    pc_run := H 0 1 (by decide) (by decide) (by decide),
    pc_big := H 0 2 (by decide) (by decide) (by decide),
    pc_logb := H 0 3 (by decide) (by decide) (by decide),
    pc_cnt := H 0 4 (by decide) (by decide) (by decide),
    pc_xb := H 0 5 (by decide) (by decide) (by decide),
    pc_xlen := H 0 6 (by decide) (by decide) (by decide),
    pc_co := H 0 7 (by decide) (by decide) (by decide),
    pc_cl := H 0 8 (by decide) (by decide) (by decide),
    pc_cap := H 0 9 (by decide) (by decide) (by decide),
    pc_one := H 0 10 (by decide) (by decide) (by decide),
    pc_zero := H 0 11 (by decide) (by decide) (by decide),
    pc_ds := H 0 12 (by decide) (by decide) (by decide),
    pc_t1 := H 0 13 (by decide) (by decide) (by decide),
    pc_t2 := H 0 14 (by decide) (by decide) (by decide),
    pc_t3 := H 0 15 (by decide) (by decide) (by decide),
    pc_t4 := H 0 16 (by decide) (by decide) (by decide),
    pc_t5 := H 0 17 (by decide) (by decide) (by decide),
    pc_t6 := H 0 18 (by decide) (by decide) (by decide),
    run_pc := (H 0 1 (by decide) (by decide) (by decide)).symm,
    run_big := H 1 2 (by decide) (by decide) (by decide),
    run_logb := H 1 3 (by decide) (by decide) (by decide),
    run_cnt := H 1 4 (by decide) (by decide) (by decide),
    run_xb := H 1 5 (by decide) (by decide) (by decide),
    run_xlen := H 1 6 (by decide) (by decide) (by decide),
    run_co := H 1 7 (by decide) (by decide) (by decide),
    run_cl := H 1 8 (by decide) (by decide) (by decide),
    run_cap := H 1 9 (by decide) (by decide) (by decide),
    run_one := H 1 10 (by decide) (by decide) (by decide),
    run_zero := H 1 11 (by decide) (by decide) (by decide),
    run_ds := H 1 12 (by decide) (by decide) (by decide),
    run_t1 := H 1 13 (by decide) (by decide) (by decide),
    run_t2 := H 1 14 (by decide) (by decide) (by decide),
    run_t3 := H 1 15 (by decide) (by decide) (by decide),
    run_t4 := H 1 16 (by decide) (by decide) (by decide),
    run_t5 := H 1 17 (by decide) (by decide) (by decide),
    run_t6 := H 1 18 (by decide) (by decide) (by decide),
    big_pc := (H 0 2 (by decide) (by decide) (by decide)).symm,
    big_run := (H 1 2 (by decide) (by decide) (by decide)).symm,
    big_logb := H 2 3 (by decide) (by decide) (by decide),
    big_cnt := H 2 4 (by decide) (by decide) (by decide),
    big_xb := H 2 5 (by decide) (by decide) (by decide),
    big_xlen := H 2 6 (by decide) (by decide) (by decide),
    big_co := H 2 7 (by decide) (by decide) (by decide),
    big_cl := H 2 8 (by decide) (by decide) (by decide),
    big_cap := H 2 9 (by decide) (by decide) (by decide),
    big_one := H 2 10 (by decide) (by decide) (by decide),
    big_zero := H 2 11 (by decide) (by decide) (by decide),
    big_ds := H 2 12 (by decide) (by decide) (by decide),
    big_t1 := H 2 13 (by decide) (by decide) (by decide),
    big_t2 := H 2 14 (by decide) (by decide) (by decide),
    big_t3 := H 2 15 (by decide) (by decide) (by decide),
    big_t4 := H 2 16 (by decide) (by decide) (by decide),
    big_t5 := H 2 17 (by decide) (by decide) (by decide),
    big_t6 := H 2 18 (by decide) (by decide) (by decide),
    logb_pc := (H 0 3 (by decide) (by decide) (by decide)).symm,
    logb_run := (H 1 3 (by decide) (by decide) (by decide)).symm,
    logb_big := (H 2 3 (by decide) (by decide) (by decide)).symm,
    logb_cnt := H 3 4 (by decide) (by decide) (by decide),
    logb_xb := H 3 5 (by decide) (by decide) (by decide),
    logb_xlen := H 3 6 (by decide) (by decide) (by decide),
    logb_co := H 3 7 (by decide) (by decide) (by decide),
    logb_cl := H 3 8 (by decide) (by decide) (by decide),
    logb_cap := H 3 9 (by decide) (by decide) (by decide),
    logb_one := H 3 10 (by decide) (by decide) (by decide),
    logb_zero := H 3 11 (by decide) (by decide) (by decide),
    logb_ds := H 3 12 (by decide) (by decide) (by decide),
    logb_t1 := H 3 13 (by decide) (by decide) (by decide),
    logb_t2 := H 3 14 (by decide) (by decide) (by decide),
    logb_t3 := H 3 15 (by decide) (by decide) (by decide),
    logb_t4 := H 3 16 (by decide) (by decide) (by decide),
    logb_t5 := H 3 17 (by decide) (by decide) (by decide),
    logb_t6 := H 3 18 (by decide) (by decide) (by decide),
    cnt_pc := (H 0 4 (by decide) (by decide) (by decide)).symm,
    cnt_run := (H 1 4 (by decide) (by decide) (by decide)).symm,
    cnt_big := (H 2 4 (by decide) (by decide) (by decide)).symm,
    cnt_logb := (H 3 4 (by decide) (by decide) (by decide)).symm,
    cnt_xb := H 4 5 (by decide) (by decide) (by decide),
    cnt_xlen := H 4 6 (by decide) (by decide) (by decide),
    cnt_co := H 4 7 (by decide) (by decide) (by decide),
    cnt_cl := H 4 8 (by decide) (by decide) (by decide),
    cnt_cap := H 4 9 (by decide) (by decide) (by decide),
    cnt_one := H 4 10 (by decide) (by decide) (by decide),
    cnt_zero := H 4 11 (by decide) (by decide) (by decide),
    cnt_ds := H 4 12 (by decide) (by decide) (by decide),
    cnt_t1 := H 4 13 (by decide) (by decide) (by decide),
    cnt_t2 := H 4 14 (by decide) (by decide) (by decide),
    cnt_t3 := H 4 15 (by decide) (by decide) (by decide),
    cnt_t4 := H 4 16 (by decide) (by decide) (by decide),
    cnt_t5 := H 4 17 (by decide) (by decide) (by decide),
    cnt_t6 := H 4 18 (by decide) (by decide) (by decide),
    xb_pc := (H 0 5 (by decide) (by decide) (by decide)).symm,
    xb_run := (H 1 5 (by decide) (by decide) (by decide)).symm,
    xb_big := (H 2 5 (by decide) (by decide) (by decide)).symm,
    xb_logb := (H 3 5 (by decide) (by decide) (by decide)).symm,
    xb_cnt := (H 4 5 (by decide) (by decide) (by decide)).symm,
    xb_xlen := H 5 6 (by decide) (by decide) (by decide),
    xb_co := H 5 7 (by decide) (by decide) (by decide),
    xb_cl := H 5 8 (by decide) (by decide) (by decide),
    xb_cap := H 5 9 (by decide) (by decide) (by decide),
    xb_one := H 5 10 (by decide) (by decide) (by decide),
    xb_zero := H 5 11 (by decide) (by decide) (by decide),
    xb_ds := H 5 12 (by decide) (by decide) (by decide),
    xb_t1 := H 5 13 (by decide) (by decide) (by decide),
    xb_t2 := H 5 14 (by decide) (by decide) (by decide),
    xb_t3 := H 5 15 (by decide) (by decide) (by decide),
    xb_t4 := H 5 16 (by decide) (by decide) (by decide),
    xb_t5 := H 5 17 (by decide) (by decide) (by decide),
    xb_t6 := H 5 18 (by decide) (by decide) (by decide),
    xlen_pc := (H 0 6 (by decide) (by decide) (by decide)).symm,
    xlen_run := (H 1 6 (by decide) (by decide) (by decide)).symm,
    xlen_big := (H 2 6 (by decide) (by decide) (by decide)).symm,
    xlen_logb := (H 3 6 (by decide) (by decide) (by decide)).symm,
    xlen_cnt := (H 4 6 (by decide) (by decide) (by decide)).symm,
    xlen_xb := (H 5 6 (by decide) (by decide) (by decide)).symm,
    xlen_co := H 6 7 (by decide) (by decide) (by decide),
    xlen_cl := H 6 8 (by decide) (by decide) (by decide),
    xlen_cap := H 6 9 (by decide) (by decide) (by decide),
    xlen_one := H 6 10 (by decide) (by decide) (by decide),
    xlen_zero := H 6 11 (by decide) (by decide) (by decide),
    xlen_ds := H 6 12 (by decide) (by decide) (by decide),
    xlen_t1 := H 6 13 (by decide) (by decide) (by decide),
    xlen_t2 := H 6 14 (by decide) (by decide) (by decide),
    xlen_t3 := H 6 15 (by decide) (by decide) (by decide),
    xlen_t4 := H 6 16 (by decide) (by decide) (by decide),
    xlen_t5 := H 6 17 (by decide) (by decide) (by decide),
    xlen_t6 := H 6 18 (by decide) (by decide) (by decide),
    co_pc := (H 0 7 (by decide) (by decide) (by decide)).symm,
    co_run := (H 1 7 (by decide) (by decide) (by decide)).symm,
    co_big := (H 2 7 (by decide) (by decide) (by decide)).symm,
    co_logb := (H 3 7 (by decide) (by decide) (by decide)).symm,
    co_cnt := (H 4 7 (by decide) (by decide) (by decide)).symm,
    co_xb := (H 5 7 (by decide) (by decide) (by decide)).symm,
    co_xlen := (H 6 7 (by decide) (by decide) (by decide)).symm,
    co_cl := H 7 8 (by decide) (by decide) (by decide),
    co_cap := H 7 9 (by decide) (by decide) (by decide),
    co_one := H 7 10 (by decide) (by decide) (by decide),
    co_zero := H 7 11 (by decide) (by decide) (by decide),
    co_ds := H 7 12 (by decide) (by decide) (by decide),
    co_t1 := H 7 13 (by decide) (by decide) (by decide),
    co_t2 := H 7 14 (by decide) (by decide) (by decide),
    co_t3 := H 7 15 (by decide) (by decide) (by decide),
    co_t4 := H 7 16 (by decide) (by decide) (by decide),
    co_t5 := H 7 17 (by decide) (by decide) (by decide),
    co_t6 := H 7 18 (by decide) (by decide) (by decide),
    cl_pc := (H 0 8 (by decide) (by decide) (by decide)).symm,
    cl_run := (H 1 8 (by decide) (by decide) (by decide)).symm,
    cl_big := (H 2 8 (by decide) (by decide) (by decide)).symm,
    cl_logb := (H 3 8 (by decide) (by decide) (by decide)).symm,
    cl_cnt := (H 4 8 (by decide) (by decide) (by decide)).symm,
    cl_xb := (H 5 8 (by decide) (by decide) (by decide)).symm,
    cl_xlen := (H 6 8 (by decide) (by decide) (by decide)).symm,
    cl_co := (H 7 8 (by decide) (by decide) (by decide)).symm,
    cl_cap := H 8 9 (by decide) (by decide) (by decide),
    cl_one := H 8 10 (by decide) (by decide) (by decide),
    cl_zero := H 8 11 (by decide) (by decide) (by decide),
    cl_ds := H 8 12 (by decide) (by decide) (by decide),
    cl_t1 := H 8 13 (by decide) (by decide) (by decide),
    cl_t2 := H 8 14 (by decide) (by decide) (by decide),
    cl_t3 := H 8 15 (by decide) (by decide) (by decide),
    cl_t4 := H 8 16 (by decide) (by decide) (by decide),
    cl_t5 := H 8 17 (by decide) (by decide) (by decide),
    cl_t6 := H 8 18 (by decide) (by decide) (by decide),
    cap_pc := (H 0 9 (by decide) (by decide) (by decide)).symm,
    cap_run := (H 1 9 (by decide) (by decide) (by decide)).symm,
    cap_big := (H 2 9 (by decide) (by decide) (by decide)).symm,
    cap_logb := (H 3 9 (by decide) (by decide) (by decide)).symm,
    cap_cnt := (H 4 9 (by decide) (by decide) (by decide)).symm,
    cap_xb := (H 5 9 (by decide) (by decide) (by decide)).symm,
    cap_xlen := (H 6 9 (by decide) (by decide) (by decide)).symm,
    cap_co := (H 7 9 (by decide) (by decide) (by decide)).symm,
    cap_cl := (H 8 9 (by decide) (by decide) (by decide)).symm,
    cap_one := H 9 10 (by decide) (by decide) (by decide),
    cap_zero := H 9 11 (by decide) (by decide) (by decide),
    cap_ds := H 9 12 (by decide) (by decide) (by decide),
    cap_t1 := H 9 13 (by decide) (by decide) (by decide),
    cap_t2 := H 9 14 (by decide) (by decide) (by decide),
    cap_t3 := H 9 15 (by decide) (by decide) (by decide),
    cap_t4 := H 9 16 (by decide) (by decide) (by decide),
    cap_t5 := H 9 17 (by decide) (by decide) (by decide),
    cap_t6 := H 9 18 (by decide) (by decide) (by decide),
    one_pc := (H 0 10 (by decide) (by decide) (by decide)).symm,
    one_run := (H 1 10 (by decide) (by decide) (by decide)).symm,
    one_big := (H 2 10 (by decide) (by decide) (by decide)).symm,
    one_logb := (H 3 10 (by decide) (by decide) (by decide)).symm,
    one_cnt := (H 4 10 (by decide) (by decide) (by decide)).symm,
    one_xb := (H 5 10 (by decide) (by decide) (by decide)).symm,
    one_xlen := (H 6 10 (by decide) (by decide) (by decide)).symm,
    one_co := (H 7 10 (by decide) (by decide) (by decide)).symm,
    one_cl := (H 8 10 (by decide) (by decide) (by decide)).symm,
    one_cap := (H 9 10 (by decide) (by decide) (by decide)).symm,
    one_zero := H 10 11 (by decide) (by decide) (by decide),
    one_ds := H 10 12 (by decide) (by decide) (by decide),
    one_t1 := H 10 13 (by decide) (by decide) (by decide),
    one_t2 := H 10 14 (by decide) (by decide) (by decide),
    one_t3 := H 10 15 (by decide) (by decide) (by decide),
    one_t4 := H 10 16 (by decide) (by decide) (by decide),
    one_t5 := H 10 17 (by decide) (by decide) (by decide),
    one_t6 := H 10 18 (by decide) (by decide) (by decide),
    zero_pc := (H 0 11 (by decide) (by decide) (by decide)).symm,
    zero_run := (H 1 11 (by decide) (by decide) (by decide)).symm,
    zero_big := (H 2 11 (by decide) (by decide) (by decide)).symm,
    zero_logb := (H 3 11 (by decide) (by decide) (by decide)).symm,
    zero_cnt := (H 4 11 (by decide) (by decide) (by decide)).symm,
    zero_xb := (H 5 11 (by decide) (by decide) (by decide)).symm,
    zero_xlen := (H 6 11 (by decide) (by decide) (by decide)).symm,
    zero_co := (H 7 11 (by decide) (by decide) (by decide)).symm,
    zero_cl := (H 8 11 (by decide) (by decide) (by decide)).symm,
    zero_cap := (H 9 11 (by decide) (by decide) (by decide)).symm,
    zero_one := (H 10 11 (by decide) (by decide) (by decide)).symm,
    zero_ds := H 11 12 (by decide) (by decide) (by decide),
    zero_t1 := H 11 13 (by decide) (by decide) (by decide),
    zero_t2 := H 11 14 (by decide) (by decide) (by decide),
    zero_t3 := H 11 15 (by decide) (by decide) (by decide),
    zero_t4 := H 11 16 (by decide) (by decide) (by decide),
    zero_t5 := H 11 17 (by decide) (by decide) (by decide),
    zero_t6 := H 11 18 (by decide) (by decide) (by decide),
    ds_pc := (H 0 12 (by decide) (by decide) (by decide)).symm,
    ds_run := (H 1 12 (by decide) (by decide) (by decide)).symm,
    ds_big := (H 2 12 (by decide) (by decide) (by decide)).symm,
    ds_logb := (H 3 12 (by decide) (by decide) (by decide)).symm,
    ds_cnt := (H 4 12 (by decide) (by decide) (by decide)).symm,
    ds_xb := (H 5 12 (by decide) (by decide) (by decide)).symm,
    ds_xlen := (H 6 12 (by decide) (by decide) (by decide)).symm,
    ds_co := (H 7 12 (by decide) (by decide) (by decide)).symm,
    ds_cl := (H 8 12 (by decide) (by decide) (by decide)).symm,
    ds_cap := (H 9 12 (by decide) (by decide) (by decide)).symm,
    ds_one := (H 10 12 (by decide) (by decide) (by decide)).symm,
    ds_zero := (H 11 12 (by decide) (by decide) (by decide)).symm,
    ds_t1 := H 12 13 (by decide) (by decide) (by decide),
    ds_t2 := H 12 14 (by decide) (by decide) (by decide),
    ds_t3 := H 12 15 (by decide) (by decide) (by decide),
    ds_t4 := H 12 16 (by decide) (by decide) (by decide),
    ds_t5 := H 12 17 (by decide) (by decide) (by decide),
    ds_t6 := H 12 18 (by decide) (by decide) (by decide),
    t1_pc := (H 0 13 (by decide) (by decide) (by decide)).symm,
    t1_run := (H 1 13 (by decide) (by decide) (by decide)).symm,
    t1_big := (H 2 13 (by decide) (by decide) (by decide)).symm,
    t1_logb := (H 3 13 (by decide) (by decide) (by decide)).symm,
    t1_cnt := (H 4 13 (by decide) (by decide) (by decide)).symm,
    t1_xb := (H 5 13 (by decide) (by decide) (by decide)).symm,
    t1_xlen := (H 6 13 (by decide) (by decide) (by decide)).symm,
    t1_co := (H 7 13 (by decide) (by decide) (by decide)).symm,
    t1_cl := (H 8 13 (by decide) (by decide) (by decide)).symm,
    t1_cap := (H 9 13 (by decide) (by decide) (by decide)).symm,
    t1_one := (H 10 13 (by decide) (by decide) (by decide)).symm,
    t1_zero := (H 11 13 (by decide) (by decide) (by decide)).symm,
    t1_ds := (H 12 13 (by decide) (by decide) (by decide)).symm,
    t1_t2 := H 13 14 (by decide) (by decide) (by decide),
    t1_t3 := H 13 15 (by decide) (by decide) (by decide),
    t1_t4 := H 13 16 (by decide) (by decide) (by decide),
    t1_t5 := H 13 17 (by decide) (by decide) (by decide),
    t1_t6 := H 13 18 (by decide) (by decide) (by decide),
    t2_pc := (H 0 14 (by decide) (by decide) (by decide)).symm,
    t2_run := (H 1 14 (by decide) (by decide) (by decide)).symm,
    t2_big := (H 2 14 (by decide) (by decide) (by decide)).symm,
    t2_logb := (H 3 14 (by decide) (by decide) (by decide)).symm,
    t2_cnt := (H 4 14 (by decide) (by decide) (by decide)).symm,
    t2_xb := (H 5 14 (by decide) (by decide) (by decide)).symm,
    t2_xlen := (H 6 14 (by decide) (by decide) (by decide)).symm,
    t2_co := (H 7 14 (by decide) (by decide) (by decide)).symm,
    t2_cl := (H 8 14 (by decide) (by decide) (by decide)).symm,
    t2_cap := (H 9 14 (by decide) (by decide) (by decide)).symm,
    t2_one := (H 10 14 (by decide) (by decide) (by decide)).symm,
    t2_zero := (H 11 14 (by decide) (by decide) (by decide)).symm,
    t2_ds := (H 12 14 (by decide) (by decide) (by decide)).symm,
    t2_t1 := (H 13 14 (by decide) (by decide) (by decide)).symm,
    t2_t3 := H 14 15 (by decide) (by decide) (by decide),
    t2_t4 := H 14 16 (by decide) (by decide) (by decide),
    t2_t5 := H 14 17 (by decide) (by decide) (by decide),
    t2_t6 := H 14 18 (by decide) (by decide) (by decide),
    t3_pc := (H 0 15 (by decide) (by decide) (by decide)).symm,
    t3_run := (H 1 15 (by decide) (by decide) (by decide)).symm,
    t3_big := (H 2 15 (by decide) (by decide) (by decide)).symm,
    t3_logb := (H 3 15 (by decide) (by decide) (by decide)).symm,
    t3_cnt := (H 4 15 (by decide) (by decide) (by decide)).symm,
    t3_xb := (H 5 15 (by decide) (by decide) (by decide)).symm,
    t3_xlen := (H 6 15 (by decide) (by decide) (by decide)).symm,
    t3_co := (H 7 15 (by decide) (by decide) (by decide)).symm,
    t3_cl := (H 8 15 (by decide) (by decide) (by decide)).symm,
    t3_cap := (H 9 15 (by decide) (by decide) (by decide)).symm,
    t3_one := (H 10 15 (by decide) (by decide) (by decide)).symm,
    t3_zero := (H 11 15 (by decide) (by decide) (by decide)).symm,
    t3_ds := (H 12 15 (by decide) (by decide) (by decide)).symm,
    t3_t1 := (H 13 15 (by decide) (by decide) (by decide)).symm,
    t3_t2 := (H 14 15 (by decide) (by decide) (by decide)).symm,
    t3_t4 := H 15 16 (by decide) (by decide) (by decide),
    t3_t5 := H 15 17 (by decide) (by decide) (by decide),
    t3_t6 := H 15 18 (by decide) (by decide) (by decide),
    t4_pc := (H 0 16 (by decide) (by decide) (by decide)).symm,
    t4_run := (H 1 16 (by decide) (by decide) (by decide)).symm,
    t4_big := (H 2 16 (by decide) (by decide) (by decide)).symm,
    t4_logb := (H 3 16 (by decide) (by decide) (by decide)).symm,
    t4_cnt := (H 4 16 (by decide) (by decide) (by decide)).symm,
    t4_xb := (H 5 16 (by decide) (by decide) (by decide)).symm,
    t4_xlen := (H 6 16 (by decide) (by decide) (by decide)).symm,
    t4_co := (H 7 16 (by decide) (by decide) (by decide)).symm,
    t4_cl := (H 8 16 (by decide) (by decide) (by decide)).symm,
    t4_cap := (H 9 16 (by decide) (by decide) (by decide)).symm,
    t4_one := (H 10 16 (by decide) (by decide) (by decide)).symm,
    t4_zero := (H 11 16 (by decide) (by decide) (by decide)).symm,
    t4_ds := (H 12 16 (by decide) (by decide) (by decide)).symm,
    t4_t1 := (H 13 16 (by decide) (by decide) (by decide)).symm,
    t4_t2 := (H 14 16 (by decide) (by decide) (by decide)).symm,
    t4_t3 := (H 15 16 (by decide) (by decide) (by decide)).symm,
    t4_t5 := H 16 17 (by decide) (by decide) (by decide),
    t4_t6 := H 16 18 (by decide) (by decide) (by decide),
    t5_pc := (H 0 17 (by decide) (by decide) (by decide)).symm,
    t5_run := (H 1 17 (by decide) (by decide) (by decide)).symm,
    t5_big := (H 2 17 (by decide) (by decide) (by decide)).symm,
    t5_logb := (H 3 17 (by decide) (by decide) (by decide)).symm,
    t5_cnt := (H 4 17 (by decide) (by decide) (by decide)).symm,
    t5_xb := (H 5 17 (by decide) (by decide) (by decide)).symm,
    t5_xlen := (H 6 17 (by decide) (by decide) (by decide)).symm,
    t5_co := (H 7 17 (by decide) (by decide) (by decide)).symm,
    t5_cl := (H 8 17 (by decide) (by decide) (by decide)).symm,
    t5_cap := (H 9 17 (by decide) (by decide) (by decide)).symm,
    t5_one := (H 10 17 (by decide) (by decide) (by decide)).symm,
    t5_zero := (H 11 17 (by decide) (by decide) (by decide)).symm,
    t5_ds := (H 12 17 (by decide) (by decide) (by decide)).symm,
    t5_t1 := (H 13 17 (by decide) (by decide) (by decide)).symm,
    t5_t2 := (H 14 17 (by decide) (by decide) (by decide)).symm,
    t5_t3 := (H 15 17 (by decide) (by decide) (by decide)).symm,
    t5_t4 := (H 16 17 (by decide) (by decide) (by decide)).symm,
    t5_t6 := H 17 18 (by decide) (by decide) (by decide),
    t6_pc := (H 0 18 (by decide) (by decide) (by decide)).symm,
    t6_run := (H 1 18 (by decide) (by decide) (by decide)).symm,
    t6_big := (H 2 18 (by decide) (by decide) (by decide)).symm,
    t6_logb := (H 3 18 (by decide) (by decide) (by decide)).symm,
    t6_cnt := (H 4 18 (by decide) (by decide) (by decide)).symm,
    t6_xb := (H 5 18 (by decide) (by decide) (by decide)).symm,
    t6_xlen := (H 6 18 (by decide) (by decide) (by decide)).symm,
    t6_co := (H 7 18 (by decide) (by decide) (by decide)).symm,
    t6_cl := (H 8 18 (by decide) (by decide) (by decide)).symm,
    t6_cap := (H 9 18 (by decide) (by decide) (by decide)).symm,
    t6_one := (H 10 18 (by decide) (by decide) (by decide)).symm,
    t6_zero := (H 11 18 (by decide) (by decide) (by decide)).symm,
    t6_ds := (H 12 18 (by decide) (by decide) (by decide)).symm,
    t6_t1 := (H 13 18 (by decide) (by decide) (by decide)).symm,
    t6_t2 := (H 14 18 (by decide) (by decide) (by decide)).symm,
    t6_t3 := (H 15 18 (by decide) (by decide) (by decide)).symm,
    t6_t4 := (H 16 18 (by decide) (by decide) (by decide)).symm,
    t6_t5 := (H 17 18 (by decide) (by decide) (by decide)).symm
  }


theorem Lay.pc_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.pc < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.pc_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.pc.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.pc_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.pc ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.run_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.run < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.run_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.run.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.run_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.run ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.big_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.big < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.big_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.big.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.big_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.big ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.logb_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.logb < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.logb_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.logb.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.logb_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.logb ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.cnt_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cnt < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.cnt_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cnt.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.cnt_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cnt ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.xb_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.xb < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.xb_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.xb.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.xb_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.xb ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.xlen_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.xlen < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.xlen_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.xlen.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.xlen_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.xlen ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.co_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.co < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.co_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.co.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.co_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.co ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.cl_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cl < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.cl_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cl.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.cl_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cl ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.cap_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cap < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.cap_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cap.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.cap_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.cap ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.one_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.one < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.one_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.one.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.one_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.one ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.zero_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.zero < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.zero_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.zero.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.zero_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.zero ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.ds_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.ds < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.ds_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.ds.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.ds_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.ds ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.t1_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t1 < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.t1_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t1.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.t1_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t1 ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.t2_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t2 < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.t2_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t2.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.t2_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t2 ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.t3_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t3 < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.t3_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t3.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.t3_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t3 ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.t4_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t4 < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.t4_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t4.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.t4_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t4 ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.t5_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t5 < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.t5_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t5.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.t5_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t5 ≠ 0 := h.nz _ (by simp [IRegs.all])
theorem Lay.t6_lt {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t6 < XB := h.lt _ (by simp [IRegs.all])
theorem Lay.t6_sz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t6.size ≤ K := h.sz _ (by simp [IRegs.all])
theorem Lay.t6_nz {r : IRegs} {B L XB K J W : ℕ} (h : Lay r B L XB K J W) : r.t6 ≠ 0 := h.nz _ (by simp [IRegs.all])


end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpB.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf



variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ}

theorem readStatic_ok (_hD : Dist r) (hl : Lay r B L XB K J W) {dst : ℕ} (x : ℕ)
    (hdst : dst ∈ r.all) (s : Store) (hB : s.mem r.big = B) :
    ∃ s' k, WExec τ J (readStatic r dst x) s s' k ∧ s'.out = s.out ∧
      s'.mem dst = s.mem (x + B) ∧ (∀ y, y ≠ r.t1 → y ≠ dst → s'.mem y = s.mem y) ∧
      k ≤ 9 * K + 3 * W + 4 * x.size + (s.mem (x + B)).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have := hl.sz _ hdst
  have := size_add_le x B
  refine ⟨_, _, WExec.seq (WExec.op _ _) (WExec.seq (WExec.op _ _) (WExec.op _ _)), ?_, ?_, ?_, ?_⟩
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]; rw [hB]
  · intro y h1 h2; simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]; rw [hB]; omega

theorem readDyn_ok (hD : Dist r) (hl : Lay r B L XB K J W) {dst ra : ℕ}
    (hdst : dst ∈ r.all) (hra : ra ∈ r.all) (s : Store) (hB : s.mem r.big = B) :
    ∃ s' k, WExec τ J (readDyn r dst ra) s s' k ∧ s'.out = s.out ∧
      s'.mem dst = s.mem (s.mem ra + B) ∧ (∀ y, y ≠ r.t1 → y ≠ dst → s'.mem y = s.mem y) ∧
      k ≤ 7 * K + 3 * W + 3 * (s.mem ra).size + (s.mem (s.mem ra + B)).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have := hl.sz _ hdst
  have := hl.sz _ hra
  have := size_add_le (s.mem ra) B
  refine ⟨_, _, WExec.seq (WExec.op _ _) (WExec.op _ _), ?_, ?_, ?_, ?_⟩
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hB]
  · intro y h1 h2; simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hB]; omega

theorem wop {p : Op} {s t : Store} (h : p.eval τ s = t) :
    WExec τ J (.op p) s t (Op.cost τ s p) := h ▸ WExec.op s p

theorem writeDyn_ok (hD : Dist r) (hl : Lay r B L XB K J W) {ra rv : ℕ}
    (hra : ra ∈ r.all) (hrv : rv ∈ r.all) (hra2 : ra ≠ r.t2) (hra3 : ra ≠ r.t3)
    (hrv2 : rv ≠ r.t2) (s : Store) {a v c : ℕ} (ha : s.mem ra = a) (hv : s.mem rv = v)
    (hcn : s.mem r.cnt = c) (hB : s.mem r.big = B) (hL : s.mem r.logb = L)
    (h1 : s.mem r.one = 1) (hc : L + c < B) :
    ∃ s' k, WExec τ J (writeDyn r ra rv) s s' k ∧ s'.out = s.out ∧
      s'.mem (a + B) = v ∧ s'.mem (L + c) = a ∧ s'.mem r.cnt = c + 1 ∧
      (∀ y, y ≠ r.t2 → y ≠ r.t3 → y ≠ r.cnt → y ≠ a + B → y ≠ L + c → s'.mem y = s.mem y) ∧
      k ≤ 14 * K + 9 * W + 4 * a.size + v.size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have := hl.sz _ hra
  have := hl.sz _ hrv
  have := hl.lt _ hra
  have := hl.lt _ hrv
  have := size_add_le a B
  have := size_mono (show L ≤ B by omega)
  have := size_mono (show c ≤ B by omega)
  have := size_mono (show L + c ≤ B by omega)
  have := size_mono (show c + 1 ≤ B by omega)
  have := Nat.size_one
  refine ⟨((((s.write r.t2 (a+B)).write (a+B) v).write r.t3 (L+c)).write (L+c) a).write r.cnt (c+1),
    _, WExec.seq (wop (t := s.write r.t2 (a+B)) ?e1)
    (WExec.seq (wop (t := (s.write r.t2 (a+B)).write (a+B) v) ?e2)
    (WExec.seq (wop (t := ((s.write r.t2 (a+B)).write (a+B) v).write r.t3 (L+c)) ?e3)
    (WExec.seq (wop (t := (((s.write r.t2 (a+B)).write (a+B) v).write r.t3 (L+c)).write (L+c) a) ?e4)
      (wop ?e5)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  case e1 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, ha, hB]
  case e2 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hv]
  case e3 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hL, hcn]
  case e4 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, ha]
  case e5 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hcn, h1]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · intro y h2 h3 h4 h5 h6; simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, ha, hv, hcn, hB, hL, h1]; omega

end TargetedSamplers.Structured.InterpPf

-- ===== Solutions/Dev/InterpC.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

def scr (r : IRegs) : List ℕ := [r.pc, r.run, r.cap, r.cnt, r.ds, r.t1, r.t2, r.t3, r.t4, r.t5, r.t6]

theorem nscr_pc {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.pc := fun e => h (by simp [scr, e])
theorem nscr_run {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.run := fun e => h (by simp [scr, e])
theorem nscr_cap {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.cap := fun e => h (by simp [scr, e])
theorem nscr_cnt {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.cnt := fun e => h (by simp [scr, e])
theorem nscr_ds {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.ds := fun e => h (by simp [scr, e])
theorem nscr_t1 {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.t1 := fun e => h (by simp [scr, e])
theorem nscr_t2 {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.t2 := fun e => h (by simp [scr, e])
theorem nscr_t3 {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.t3 := fun e => h (by simp [scr, e])
theorem nscr_t4 {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.t4 := fun e => h (by simp [scr, e])
theorem nscr_t5 {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.t5 := fun e => h (by simp [scr, e])
theorem nscr_t6 {r : IRegs} {y : ℕ} (h : y ∉ scr r) : y ≠ r.t6 := fun e => h (by simp [scr, e])

theorem big_nscr {r : IRegs} (hD : Dist r) : r.big ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.big_pc, hD.big_run, hD.big_cap, hD.big_cnt, hD.big_ds, hD.big_t1, hD.big_t2, hD.big_t3, hD.big_t4, hD.big_t5, hD.big_t6⟩
theorem logb_nscr {r : IRegs} (hD : Dist r) : r.logb ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.logb_pc, hD.logb_run, hD.logb_cap, hD.logb_cnt, hD.logb_ds, hD.logb_t1, hD.logb_t2, hD.logb_t3, hD.logb_t4, hD.logb_t5, hD.logb_t6⟩
theorem xb_nscr {r : IRegs} (hD : Dist r) : r.xb ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.xb_pc, hD.xb_run, hD.xb_cap, hD.xb_cnt, hD.xb_ds, hD.xb_t1, hD.xb_t2, hD.xb_t3, hD.xb_t4, hD.xb_t5, hD.xb_t6⟩
theorem xlen_nscr {r : IRegs} (hD : Dist r) : r.xlen ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.xlen_pc, hD.xlen_run, hD.xlen_cap, hD.xlen_cnt, hD.xlen_ds, hD.xlen_t1, hD.xlen_t2, hD.xlen_t3, hD.xlen_t4, hD.xlen_t5, hD.xlen_t6⟩
theorem co_nscr {r : IRegs} (hD : Dist r) : r.co ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.co_pc, hD.co_run, hD.co_cap, hD.co_cnt, hD.co_ds, hD.co_t1, hD.co_t2, hD.co_t3, hD.co_t4, hD.co_t5, hD.co_t6⟩
theorem cl_nscr {r : IRegs} (hD : Dist r) : r.cl ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.cl_pc, hD.cl_run, hD.cl_cap, hD.cl_cnt, hD.cl_ds, hD.cl_t1, hD.cl_t2, hD.cl_t3, hD.cl_t4, hD.cl_t5, hD.cl_t6⟩
theorem one_nscr {r : IRegs} (hD : Dist r) : r.one ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.one_pc, hD.one_run, hD.one_cap, hD.one_cnt, hD.one_ds, hD.one_t1, hD.one_t2, hD.one_t3, hD.one_t4, hD.one_t5, hD.one_t6⟩
theorem zero_nscr {r : IRegs} (hD : Dist r) : r.zero ∉ scr r := by
  simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hD.zero_pc, hD.zero_run, hD.zero_cap, hD.zero_cnt, hD.zero_ds, hD.zero_t1, hD.zero_t2, hD.zero_t3, hD.zero_t4, hD.zero_t5, hD.zero_t6⟩

theorem scr_sub {r : IRegs} {y : ℕ} (h : y ∈ scr r) : y ∈ r.all := by
  simp only [scr, IRegs.all, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto

theorem high_nscr {r : IRegs} {B L XB K J W : ℕ} (hl : Lay r B L XB K J W) {y : ℕ} (h : XB ≤ y) :
    y ∉ scr r := fun hm => by have := hl.lt y (scr_sub hm); omega

theorem cell0_nscr {r : IRegs} {B L XB K J W : ℕ} (hl : Lay r B L XB K J W) : 0 ∉ scr r :=
  fun hm => hl.nz 0 (scr_sub hm) rfl

structure Env (r : IRegs) (B L XB : ℕ) (x : List Bool) (co cl : ℕ) (S0 : Store) : Prop where
  big : S0.mem r.big = B
  logb : S0.mem r.logb = L
  xb : S0.mem r.xb = XB
  xlen : S0.mem r.xlen = x.length
  co : S0.mem r.co = co
  cl : S0.mem r.cl = cl
  one : S0.mem r.one = 1
  zero : S0.mem r.zero = 0
  z0 : S0.mem 0 = 0
  inp : ∀ i (hi : i < x.length), S0.mem (XB + i) = (x[i]'hi).toNat
  xin : XB + x.length ≤ L

structure Inv (r : IRegs) (B L : ℕ) (S0 S : Store) (pc : ℕ) (out : List Bool) (mem : ℕ → ℕ)
    (work cnt : ℕ) : Prop where
  hpc : S.mem r.pc = pc
  hcap : S.mem r.cap = capValue out
  hcnt : S.mem r.cnt = cnt
  sim : ∀ u, S.mem (u + B) = mem u
  logged : ∀ u, mem u ≠ 0 → ∃ j < cnt, S.mem (L + j) = u
  cost : cnt + ∑ j ∈ Finset.range cnt, (S.mem (L + j)).size ≤ work
  frame : ∀ y, y ∉ scr r → (y < L ∨ (L + cnt ≤ y ∧ y < B)) → S.mem y = S0.mem y
  hout : S.out = S0.out

section
variable {r : IRegs} {B L XB K J W : ℕ} {x : List Bool} {co cl : ℕ} {S0 S : Store} {pc : ℕ}
  {out : List Bool} {mem : ℕ → ℕ} {work cnt : ℕ}

theorem Inv.fixed (_hl : Lay r B L XB K J W) (hI : Inv r B L S0 S pc out mem work cnt) {y : ℕ}
    (hy : y ∉ scr r) (hyL : y < L) : S.mem y = S0.mem y := hI.frame y hy (Or.inl hyL)

theorem Inv.big (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.big = B := by
  have := hl.big_lt; have := hl.xl
  rw [hI.fixed hl (big_nscr hD) (by omega), he.big]
theorem Inv.logb (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.logb = L := by
  have := hl.logb_lt; have := hl.xl
  rw [hI.fixed hl (logb_nscr hD) (by omega), he.logb]
theorem Inv.xb (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.xb = XB := by
  have := hl.xb_lt; have := hl.xl
  rw [hI.fixed hl (xb_nscr hD) (by omega), he.xb]
theorem Inv.xlen (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.xlen = x.length := by
  have := hl.xlen_lt; have := hl.xl
  rw [hI.fixed hl (xlen_nscr hD) (by omega), he.xlen]
theorem Inv.vco (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.co = co := by
  have := hl.co_lt; have := hl.xl
  rw [hI.fixed hl (co_nscr hD) (by omega), he.co]
theorem Inv.vcl (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.cl = cl := by
  have := hl.cl_lt; have := hl.xl
  rw [hI.fixed hl (cl_nscr hD) (by omega), he.cl]
theorem Inv.one (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.one = 1 := by
  have := hl.one_lt; have := hl.xl
  rw [hI.fixed hl (one_nscr hD) (by omega), he.one]
theorem Inv.zero (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem r.zero = 0 := by
  have := hl.zero_lt; have := hl.xl
  rw [hI.fixed hl (zero_nscr hD) (by omega), he.zero]
theorem Inv.z0 (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) : S.mem 0 = 0 := by
  have := hl.pc_lt; have := hl.xl
  rw [hI.fixed hl (cell0_nscr hl) (by omega), he.z0]
theorem Inv.inp (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (i : ℕ) (hi : i < x.length) :
    S.mem (XB + i) = (x[i]'hi).toNat := by
  have := he.xin
  rw [hI.fixed hl (high_nscr hl (by omega)) (by omega), he.inp]

theorem inv_move (hl : Lay r B L XB K J W) (hI : Inv r B L S0 S pc out mem work cnt)
    {S' : Store} {p' work' : ℕ} {out' : List Bool}
    (hf : ∀ y, y ∉ scr r → S'.mem y = S.mem y) (hpc : S'.mem r.pc = p')
    (hcap : S'.mem r.cap = capValue out') (hcnt : S'.mem r.cnt = S.mem r.cnt)
    (ho : S'.out = S.out) (hw : work ≤ work') : Inv r B L S0 S' p' out' mem work' cnt := by
  have := hl.xl; have := hl.lb
  refine ⟨hpc, hcap, hcnt.trans hI.hcnt, fun u => ?_, fun u hu => ?_, ?_, fun y hy h => ?_,
    ho.trans hI.hout⟩
  · rw [hf _ (high_nscr hl (by omega)), hI.sim]
  · obtain ⟨j, hj, e⟩ := hI.logged u hu
    exact ⟨j, hj, by rw [hf _ (high_nscr hl (by omega)), e]⟩
  · have : ∑ j ∈ Finset.range cnt, (S'.mem (L + j)).size =
        ∑ j ∈ Finset.range cnt, (S.mem (L + j)).size :=
      Finset.sum_congr rfl fun j _ => by rw [hf _ (high_nscr hl (by omega))]
    have := hI.cost; omega
  · rw [hf y hy, hI.frame y hy h]

theorem inv_write (hl : Lay r B L XB K J W) (hI : Inv r B L S0 S pc out mem work cnt)
    {S' : Store} {p' work' a v : ℕ}
    (hf : ∀ y, y ∉ scr r → y ≠ a + B → y ≠ L + cnt → S'.mem y = S.mem y)
    (hav : S'.mem (a + B) = v) (hlog : S'.mem (L + cnt) = a) (hpc : S'.mem r.pc = p')
    (hcap : S'.mem r.cap = S.mem r.cap) (hcnt : S'.mem r.cnt = cnt + 1)
    (ho : S'.out = S.out) (hroom : L + cnt < B) (hw : work + 1 + a.size ≤ work') :
    Inv r B L S0 S' p' out (Function.update mem a v) work' (cnt + 1) := by
  have := hl.xl; have := hl.lb
  refine ⟨hpc, hcap.trans hI.hcap, hcnt, fun u => ?_, fun u hu => ?_, ?_, fun y hy h => ?_,
    ho.trans hI.hout⟩
  · by_cases hu : u = a
    · subst hu; rw [hav, Function.update_self]
    · rw [hf _ (high_nscr hl (by omega)) (by omega) (by omega), hI.sim,
        Function.update_of_ne hu]
  · by_cases hua : u = a
    · subst hua; exact ⟨cnt, by omega, hlog⟩
    · rw [Function.update_of_ne hua] at hu
      obtain ⟨j, hj, e⟩ := hI.logged u hu
      exact ⟨j, by omega, by rw [hf _ (high_nscr hl (by omega)) (by omega) (by omega), e]⟩
  · rw [Finset.sum_range_succ, hlog]
    have : ∑ j ∈ Finset.range cnt, (S'.mem (L + j)).size =
        ∑ j ∈ Finset.range cnt, (S.mem (L + j)).size :=
      Finset.sum_congr rfl fun j hj => by
        rw [Finset.mem_range] at hj
        rw [hf _ (high_nscr hl (by omega)) (by omega) (by omega)]
    have := hI.cost; omega
  · rw [hf y hy (by omega) (by omega), hI.frame y hy (by omega)]

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpD.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

section
variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ} {x : List Bool} {co cl : ℕ}
  {S0 S : Store} {pc : ℕ} {out : List Bool} {mem : ℕ → ℕ} {work cnt : ℕ}

theorem setPC_ok (s : Store) (p : ℕ) :
    WExec τ J (setPC r p) s (s.write r.pc p) (1 + r.pc.size + p.size) := WExec.op s _

theorem inv_frame (hl : Lay r B L XB K J W) (hI : Inv r B L S0 S pc out mem work cnt)
    {S' : Store} (hf : ∀ y, y ∉ scr r → S'.mem y = S.mem y) (hpc : S'.mem r.pc = S.mem r.pc)
    (hcap : S'.mem r.cap = S.mem r.cap) (hcnt : S'.mem r.cnt = S.mem r.cnt)
    (ho : S'.out = S.out) : Inv r B L S0 S' pc out mem work cnt :=
  inv_move hl hI hf (hpc.trans hI.hpc) (hcap.trans hI.hcap) hcnt ho le_rfl

theorem core_dyn (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) {ra rv : ℕ}
    (hra : ra ∈ r.all) (hrv : rv ∈ r.all) (hra2 : ra ≠ r.t2) (hra3 : ra ≠ r.t3)
    (hrv2 : rv ≠ r.t2) {a v : ℕ} (ha : S.mem ra = a) (hv : S.mem rv = v) (p' work' : ℕ)
    (hw : work + 1 + a.size ≤ work') :
    ∃ S1 k, WExec τ J (writeDyn r ra rv) S S1 k ∧
      Inv r B L S0 (S1.write r.pc p') p' out (Function.update mem a v) work' (cnt + 1) ∧
      (S1.write r.pc p').mem r.run = S.mem r.run ∧
      k + (1 + r.pc.size + p'.size) ≤ 16 * K + 9 * W + 4 * a.size + v.size + p'.size := by
  obtain ⟨S1, k1, e1, o1, h1a, h1l, h1c, f1, c1⟩ := writeDyn_ok (τ := τ) (J := J) hD hl hra hrv
    hra2 hra3 hrv2 S ha hv hI.hcnt (hI.big hD hl he) (hI.logb hD hl he) (hI.one hD hl he) hroom
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  refine ⟨S1, _, e1, inv_write hl hI ?_ ?_ ?_ ?_ ?_ ?_ ?_ hroom hw, ?_, ?_⟩
  · intro y hy h1 h2
    rw [write_mem_ne _ _ (nscr_pc hy), f1 y (nscr_t2 hy) (nscr_t3 hy) (nscr_cnt hy) h1 h2]
  · rw [write_mem_ne _ _ (by omega), h1a]
  · rw [write_mem_ne _ _ (by omega), h1l]
  · rw [write_mem_self]
  · rw [write_mem_ne _ _ hD.cap_pc, f1 _ hD.cap_t2 hD.cap_t3 hD.cap_cnt (by omega) (by omega)]
  · rw [write_mem_ne _ _ hD.cnt_pc, h1c]
  · rw [write_out, o1]
  · rw [write_mem_ne _ _ hD.run_pc, f1 _ hD.run_t2 hD.run_t3 hD.run_cnt (by omega) (by omega)]
  · omega

theorem tail_dyn (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) {ra rv : ℕ}
    (hra : ra ∈ r.all) (hrv : rv ∈ r.all) (hra2 : ra ≠ r.t2) (hra3 : ra ≠ r.t3)
    (hrv2 : rv ≠ r.t2) {a v : ℕ} (ha : S.mem ra = a) (hv : S.mem rv = v) (p' work' : ℕ)
    (hw : work + 1 + a.size ≤ work') :
    ∃ S' k, WExec τ J (.seq (writeDyn r ra rv) (setPC r p')) S S' k ∧
      Inv r B L S0 S' p' out (Function.update mem a v) work' (cnt + 1) ∧
      S'.mem r.run = S.mem r.run ∧ k ≤ 16 * K + 9 * W + 4 * a.size + v.size + p'.size := by
  obtain ⟨S1, k1, e1, hI1, hr1, c1⟩ := core_dyn (τ := τ) (J := J) hD hl he hI hroom hra hrv
    hra2 hra3 hrv2 ha hv p' work' hw
  exact ⟨_, _, WExec.seq e1 (setPC_ok _ _), hI1, hr1, c1⟩

theorem tail_static (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) {rv : ℕ}
    (hrv : rv ∈ r.all) (hrv2 : rv ≠ r.t2) (hrv4 : rv ≠ r.t4) {v : ℕ} (hv : S.mem rv = v)
    (d p' work' : ℕ) (hw : work + 1 + d.size ≤ work') :
    ∃ S' k, WExec τ J (.seq (writeStatic r d rv) (setPC r p')) S S' k ∧
      Inv r B L S0 S' p' out (Function.update mem d v) work' (cnt + 1) ∧
      S'.mem r.run = S.mem r.run ∧ k ≤ 18 * K + 9 * W + 5 * d.size + v.size + p'.size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have hI0 : Inv r B L S0 (S.write r.t4 d) pc out mem work cnt :=
    inv_frame hl hI (fun y hy => write_mem_ne _ _ (nscr_t4 hy)) (write_mem_ne _ _ hD.pc_t4)
      (write_mem_ne _ _ hD.cap_t4) (write_mem_ne _ _ hD.cnt_t4) rfl
  obtain ⟨S1, k1, e1, hI1, hr1, c1⟩ := core_dyn (τ := τ) (J := J) hD hl he hI0 hroom
    (ra := r.t4) (rv := rv) (by simp [IRegs.all]) hrv hD.t4_t2 hD.t4_t3 hrv2 (write_mem_self _ _ _)
    (by rw [write_mem_ne _ _ hrv4, hv]) p' work' hw
  refine ⟨_, _, WExec.seq (WExec.seq (WExec.op _ _) e1) (setPC_ok _ _), hI1,
    by rw [hr1, write_mem_ne _ _ hD.run_t4], ?_⟩
  simp only [Op.cost]; omega

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpE.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

section
variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ} {x : List Bool} {co cl : ℕ}
  {S0 S : Store} {pc : ℕ} {out : List Bool} {mem : ℕ → ℕ} {work cnt : ℕ}

theorem inv_wr (hl : Lay r B L XB K J W) (hI : Inv r B L S0 S pc out mem work cnt) {d : ℕ}
    (v : ℕ) (hd : d ∈ scr r) (hpc : r.pc ≠ d) (hcap : r.cap ≠ d) (hcnt : r.cnt ≠ d) :
    Inv r B L S0 (S.write d v) pc out mem work cnt :=
  inv_frame hl hI (fun y hy => write_mem_ne _ _ (fun e => hy (e ▸ hd))) (write_mem_ne _ _ hpc)
    (write_mem_ne _ _ hcap) (write_mem_ne _ _ hcnt) rfl

theorem rs_inv (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) {dst : ℕ} (hdst : dst = r.t5 ∨ dst = r.t6)
    (a : ℕ) :
    ∃ S1 k, WExec τ J (readStatic r dst a) S S1 k ∧ Inv r B L S0 S1 pc out mem work cnt ∧
      S1.mem dst = mem a ∧ (∀ y, y ≠ r.t1 → y ≠ dst → S1.mem y = S.mem y) ∧
      k ≤ 9 * K + 3 * W + 4 * a.size + (mem a).size := by
  have hm : dst ∈ r.all := by rcases hdst with rfl | rfl <;> simp [IRegs.all]
  have hn : ∀ y, y ∉ scr r → y ≠ dst := by
    rcases hdst with rfl | rfl
    exacts [fun y => nscr_t5, fun y => nscr_t6]
  have h1 : r.pc ≠ dst := by rcases hdst with rfl | rfl <;> (have hD__ := ‹Dist _›; cases hD__; assumption)
  have h2 : r.cap ≠ dst := by rcases hdst with rfl | rfl <;> (have hD__ := ‹Dist _›; cases hD__; assumption)
  have h3 : r.cnt ≠ dst := by rcases hdst with rfl | rfl <;> (have hD__ := ‹Dist _›; cases hD__; assumption)
  obtain ⟨S1, k, e, o, hv, f, c⟩ := readStatic_ok (τ := τ) (J := J) hD hl a hm S (hI.big hD hl he)
  rw [hI.sim] at hv c
  exact ⟨S1, k, e, inv_frame hl hI (fun y hy => f y (nscr_t1 hy) (hn y hy))
    (f _ hD.pc_t1 h1) (f _ hD.cap_t1 h2) (f _ hD.cnt_t1 h3) o, hv, f, c⟩

theorem rd_inv (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) {u : ℕ} (hu : S.mem r.t5 = u) :
    ∃ S1 k, WExec τ J (readDyn r r.t6 r.t5) S S1 k ∧ Inv r B L S0 S1 pc out mem work cnt ∧
      S1.mem r.t6 = mem u ∧ (∀ y, y ≠ r.t1 → y ≠ r.t6 → S1.mem y = S.mem y) ∧
      k ≤ 7 * K + 3 * W + 3 * u.size + (mem u).size := by
  obtain ⟨S1, k, e, o, hv, f, c⟩ := readDyn_ok (τ := τ) (J := J) hD hl (dst := r.t6) (ra := r.t5)
    (by simp [IRegs.all]) (by simp [IRegs.all]) S (hI.big hD hl he)
  rw [hu, hI.sim] at hv c
  exact ⟨S1, k, e, inv_frame hl hI (fun y hy => f y (nscr_t1 hy) (nscr_t6 hy))
    (f _ hD.pc_t1 hD.pc_t6) (f _ hD.cap_t1 hD.cap_t6) (f _ hD.cnt_t1 hD.cnt_t6) o, hv, f, c⟩

theorem hd_const (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p d c : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.const d c)) S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem d c) (work + 1 + d.size + c.size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + d.size + c.size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have hI1 := inv_wr hl hI c (d := r.t5) (by simp [scr]) hD.pc_t5 hD.cap_t5 hD.cnt_t5
  obtain ⟨S2, k2, e2, hI2, hr2, c2⟩ := tail_static (τ := τ) (J := J) hD hl he hI1 hroom
    (rv := r.t5) (by simp [IRegs.all]) hD.t5_t2 hD.t5_t4 (write_mem_self _ _ _) d (p+1)
    (work + 1 + d.size + c.size) (by omega)
  refine ⟨S2, _, WExec.seq (WExec.op _ _) e2, hI2, by rw [hr2, write_mem_ne _ _ hD.run_t5], ?_⟩
  simp only [Op.cost]; omega

theorem hd_lit (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p d c work' : ℕ)
    (hc : c ≤ 2) (hw : work + 1 + d.size ≤ work') :
    ∃ S' k, WExec τ J (.seq (.op (.const r.t6 c)) (.seq (writeStatic r d r.t6) (setPC r (p+1))))
        S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem d c) work' (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + d.size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have := size_mono hc
  have : (2:ℕ).size = 2 := by decide
  have hI1 := inv_wr hl hI c (d := r.t6) (by simp [scr]) hD.pc_t6 hD.cap_t6 hD.cnt_t6
  obtain ⟨S2, k2, e2, hI2, hr2, c2⟩ := tail_static (τ := τ) (J := J) hD hl he hI1 hroom
    (rv := r.t6) (by simp [IRegs.all]) hD.t6_t2 hD.t6_t4 (write_mem_self _ _ _) d (p+1)
    work' hw
  refine ⟨S2, _, WExec.seq (WExec.op _ _) e2, hI2, by rw [hr2, write_mem_ne _ _ hD.run_t6], ?_⟩
  simp only [Op.cost]; omega

theorem hd_inputLength (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p d : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.inputLength d)) S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem d x.length)
        (work + 1 + d.size + x.length.size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + d.size + x.length.size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S2, k2, e2, hI2, hr2, c2⟩ := tail_static (τ := τ) (J := J) hD hl he hI hroom
    (rv := r.xlen) (by simp [IRegs.all]) hD.xlen_t2 hD.xlen_t4 (hI.xlen hD hl he) d (p+1)
    (work + 1 + d.size + x.length.size) (by omega)
  exact ⟨S2, _, e2, hI2, hr2, by omega⟩

theorem hd_halt (hD : Dist r) (hl : Lay r B L XB K J W)
    (hI : Inv r B L S0 S pc out mem work cnt) :
    ∃ S' k, WExec τ J (.op (.const r.run 0)) S S' k ∧
      Inv r B L S0 S' pc out mem (work + 1) cnt ∧ S'.mem r.run = 0 ∧ k ≤ 1 + K := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  refine ⟨_, _, WExec.op _ _, inv_wr hl hI 0 (d := r.run) (by simp [scr]) hD.pc_run hD.cap_run
    hD.cnt_run |> fun h => inv_move hl h (fun _ _ => rfl) h.hpc h.hcap rfl rfl (by omega),
    write_mem_self _ _ _, ?_⟩
  simp only [Op.cost, Nat.size_zero]; omega

theorem hd_add (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p d a b : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.add d a b)) S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem d (mem a + mem b))
        (work + 1 + d.size + a.size + b.size + (mem a).size + (mem b).size +
          (mem a + mem b).size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + d.size + a.size + b.size + (mem a).size + (mem b).size +
          (mem a + mem b).size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  obtain ⟨S2, k2, e2, hI2, hv2, f2, c2⟩ := rs_inv (τ := τ) (J := J) hD hl he hI1 (Or.inr rfl) b
  have hu2 : S2.mem r.t5 = mem a := by rw [f2 _ hD.t5_t1 hD.t5_t6, hv1]
  have hI3 := inv_wr hl hI2 (mem a + mem b) (d := r.t5) (by simp [scr]) hD.pc_t5 hD.cap_t5
    hD.cnt_t5
  obtain ⟨S4, k4, e4, hI4, hr4, c4⟩ := tail_static (τ := τ) (J := J) hD hl he hI3 hroom
    (rv := r.t5) (by simp [IRegs.all]) hD.t5_t2 hD.t5_t4 (write_mem_self _ _ _) d (p+1)
    (work + 1 + d.size + a.size + b.size + (mem a).size + (mem b).size + (mem a + mem b).size)
    (by omega)
  refine ⟨S4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq (wop ?ev) e4)), hI4, ?_, ?_⟩
  case ev => simp only [Op.eval, hu2, hv2]
  · rw [hr4, write_mem_ne _ _ hD.run_t5, f2 _ hD.run_t1 hD.run_t6, f1 _ hD.run_t1 hD.run_t5]
  · simp only [Op.cost, hu2, hv2]; omega

theorem hd_monus (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p d a b : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.monus d a b)) S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem d (mem a - mem b))
        (work + 1 + d.size + a.size + b.size + (mem a).size + (mem b).size +
          (mem a - mem b).size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + d.size + a.size + b.size + (mem a).size + (mem b).size +
          (mem a - mem b).size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  obtain ⟨S2, k2, e2, hI2, hv2, f2, c2⟩ := rs_inv (τ := τ) (J := J) hD hl he hI1 (Or.inr rfl) b
  have hu2 : S2.mem r.t5 = mem a := by rw [f2 _ hD.t5_t1 hD.t5_t6, hv1]
  have hI3 := inv_wr hl hI2 (mem a - mem b) (d := r.t5) (by simp [scr]) hD.pc_t5 hD.cap_t5
    hD.cnt_t5
  obtain ⟨S4, k4, e4, hI4, hr4, c4⟩ := tail_static (τ := τ) (J := J) hD hl he hI3 hroom
    (rv := r.t5) (by simp [IRegs.all]) hD.t5_t2 hD.t5_t4 (write_mem_self _ _ _) d (p+1)
    (work + 1 + d.size + a.size + b.size + (mem a).size + (mem b).size + (mem a - mem b).size)
    (by omega)
  refine ⟨S4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq (wop ?ev) e4)), hI4, ?_, ?_⟩
  case ev => simp only [Op.eval, hu2, hv2]
  · rw [hr4, write_mem_ne _ _ hD.run_t5, f2 _ hD.run_t1 hD.run_t6, f1 _ hD.run_t1 hD.run_t5]
  · simp only [Op.cost, hu2, hv2]; omega

theorem hd_load (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p d a : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.load d a)) S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem d (mem (mem a)))
        (work + 1 + d.size + a.size + (mem a).size + (mem (mem a)).size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + d.size + a.size + (mem a).size + (mem (mem a)).size) +
        (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  obtain ⟨S2, k2, e2, hI2, hv2, f2, c2⟩ := rd_inv (τ := τ) (J := J) hD hl he hI1 hv1
  obtain ⟨S4, k4, e4, hI4, hr4, c4⟩ := tail_static (τ := τ) (J := J) hD hl he hI2 hroom
    (rv := r.t6) (by simp [IRegs.all]) hD.t6_t2 hD.t6_t4 hv2 d (p+1)
    (work + 1 + d.size + a.size + (mem a).size + (mem (mem a)).size) (by omega)
  refine ⟨S4, _, WExec.seq e1 (WExec.seq e2 e4), hI4, ?_, ?_⟩
  · rw [hr4, f2 _ hD.run_t1 hD.run_t6, f1 _ hD.run_t1 hD.run_t5]
  · omega

theorem hd_store (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p a b : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.store a b)) S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem (mem a) (mem b))
        (work + 1 + a.size + b.size + (mem a).size + (mem b).size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + a.size + b.size + (mem a).size + (mem b).size) +
        (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  obtain ⟨S2, k2, e2, hI2, hv2, f2, c2⟩ := rs_inv (τ := τ) (J := J) hD hl he hI1 (Or.inr rfl) b
  have hu2 : S2.mem r.t5 = mem a := by rw [f2 _ hD.t5_t1 hD.t5_t6, hv1]
  obtain ⟨S4, k4, e4, hI4, hr4, c4⟩ := tail_dyn (τ := τ) (J := J) hD hl he hI2 hroom
    (ra := r.t5) (rv := r.t6) (by simp [IRegs.all]) (by simp [IRegs.all]) hD.t5_t2 hD.t5_t3
    hD.t6_t2 hu2 hv2 (p+1) (work + 1 + a.size + b.size + (mem a).size + (mem b).size)
    (by omega)
  refine ⟨S4, _, WExec.seq e1 (WExec.seq e2 e4), hI4, ?_, ?_⟩
  · rw [hr4, f2 _ hD.run_t1 hD.run_t6, f1 _ hD.run_t1 hD.run_t5]
  · omega

theorem hd_jle (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (p a b tg : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.jle a b tg)) S S' k ∧
      Inv r B L S0 S' (if mem a ≤ mem b then tg else p + 1) out mem
        (work + 1 + a.size + b.size + (mem a).size + (mem b).size + tg.size) cnt ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + a.size + b.size + (mem a).size + (mem b).size + tg.size) +
        (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  obtain ⟨S2, k2, e2, hI2, hv2, f2, c2⟩ := rs_inv (τ := τ) (J := J) hD hl he hI1 (Or.inr rfl) b
  have hu2 : S2.mem r.t5 = mem a := by rw [f2 _ hD.t5_t1 hD.t5_t6, hv1]
  have hrun : S2.mem r.run = S.mem r.run := by
    rw [f2 _ hD.run_t1 hD.run_t6, f1 _ hD.run_t1 hD.run_t5]
  have hz := hI2.z0 hl he
  have hinv : ∀ q, Inv r B L S0 (S2.write r.pc q) q out mem
      (work + 1 + a.size + b.size + (mem a).size + (mem b).size + tg.size) cnt := fun q =>
    inv_move hl hI2 (fun y hy => write_mem_ne _ _ (nscr_pc hy)) (write_mem_self _ _ _)
      (by rw [write_mem_ne _ _ hD.cap_pc]; exact hI2.hcap) (write_mem_ne _ _ hD.cnt_pc) rfl
      (by omega)
  by_cases h : mem a ≤ mem b
  · refine ⟨S2.write r.pc tg, _, WExec.seq e1 (WExec.seq e2
      (WExec.yes (by rw [hu2, hv2]; exact h) (setPC_ok _ _))), by rw [if_pos h]; exact hinv _,
      by rw [write_mem_ne _ _ hD.run_pc, hrun], ?_⟩
    simp only [jumpCost, hu2, hv2]; omega
  · refine ⟨S2.write r.pc (p+1), _, WExec.seq e1 (WExec.seq e2
      (WExec.no (by rw [hu2, hv2]; exact h) (setPC_ok _ _))), by rw [if_neg h]; exact hinv _,
      by rw [write_mem_ne _ _ hD.run_pc, hrun], ?_⟩
    simp only [jumpCost, hu2, hv2, write_mem_ne _ _ (Ne.symm hl.pc_nz), hz, Nat.size_zero]
    omega

theorem capValue_snoc (l : List Bool) (b : Bool) : capValue (l ++ [b]) = b.toNat := by
  simp [capValue]

theorem hd_output (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (p a : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.output a)) S S' k ∧
      Inv r B L S0 S' (p + 1) (out ++ [mem a != 0]) mem (work + 1 + a.size + (mem a).size) cnt ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + a.size + (mem a).size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  have hrun : S1.mem r.run = S.mem r.run := f1 _ hD.run_t1 hD.run_t5
  have hz := hI1.z0 hl he
  have hzr := hI1.zero hD hl he
  have hinv : ∀ c : ℕ, c = (mem a != 0).toNat → Inv r B L S0 ((S1.write r.cap c).write r.pc (p+1))
      (p+1) (out ++ [mem a != 0]) mem (work + 1 + a.size + (mem a).size) cnt := fun c hc =>
    inv_move hl hI1 (fun y hy => by
        rw [write_mem_ne _ _ (nscr_pc hy), write_mem_ne _ _ (nscr_cap hy)])
      (write_mem_self _ _ _)
      (by rw [write_mem_ne _ _ hD.cap_pc, write_mem_self, capValue_snoc, hc])
      (by rw [write_mem_ne _ _ hD.cnt_pc, write_mem_ne _ _ hD.cnt_cap]) rfl (by omega)
  have hrun' : ∀ c : ℕ, ((S1.write r.cap c).write r.pc (p+1)).mem r.run = S.mem r.run := fun c => by
    rw [write_mem_ne _ _ hD.run_pc, write_mem_ne _ _ hD.run_cap, hrun]
  by_cases h : mem a = 0
  · refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.yes (by rw [hv1, hzr]; omega) (WExec.op _ _))
      (setPC_ok _ _)), hinv 0 (by simp [h]), hrun' 0, ?_⟩
    simp only [jumpCost, Op.cost, hv1, hzr, Nat.size_zero]; omega
  · refine ⟨_, _, WExec.seq e1 (WExec.seq (WExec.no (by rw [hv1, hzr]; omega) (WExec.op _ _))
      (setPC_ok _ _)), hinv 1 (by rw [bne_iff_ne.mpr h]; rfl), hrun' 1, ?_⟩
    simp only [jumpCost, Op.cost, Op.eval, hv1, hzr, Nat.size_zero, Nat.size_one,
      write_mem_ne _ _ (Ne.symm hl.cap_nz), hz]
    omega

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpF.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

theorem windowCoins_get (cs : List Bool) (co cl u : ℕ) :
    (windowCoins cs co cl)[u]? = if u < cl then some ((cs[co+u]?).getD false) else none := by
  unfold windowCoins
  split_ifs with h
  · simp [List.getElem?_ofFn, h]
  · simp; omega

theorem size_two : (2:ℕ).size = 2 := by decide

section
variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ} {x : List Bool} {co cl : ℕ}
  {S0 S : Store} {pc : ℕ} {out : List Bool} {mem : ℕ → ℕ} {work cnt : ℕ}

theorem blk_input (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) {u : ℕ} (hu : S.mem r.t5 = u) :
    ∃ S' k, WExec τ J (.branch r.xlen r.t5 (.op (.const r.t6 2))
        (.seq (.op (.add r.t1 r.xb r.t5)) (.op (.load r.t6 r.t1)))) S S' k ∧
      Inv r B L S0 S' pc out mem work cnt ∧ S'.mem r.t6 = bitVal x[u]? ∧
      S'.mem r.run = S.mem r.run ∧ k ≤ 10 * K + 8 * W + 2 * u.size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have hxl := hI.xlen hD hl he
  have hxb := hI.xb hD hl he
  have hz := hI.z0 hl he
  have := he.xin
  have := size_mono (show x.length ≤ B by omega)
  have := size_mono (show XB ≤ B by omega)
  have := size_two
  by_cases h : x.length ≤ u
  · refine ⟨S.write r.t6 2, _, WExec.yes (by rw [hxl, hu]; exact h) (WExec.op _ _),
      inv_wr hl hI 2 (d := r.t6) (by simp [scr]) hD.pc_t6 hD.cap_t6 hD.cnt_t6,
      by rw [write_mem_self, List.getElem?_eq_none h]; rfl, write_mem_ne _ _ hD.run_t6, ?_⟩
    simp only [jumpCost, Op.cost, hxl, hu]; omega
  · have hlt : u < x.length := by omega
    have := size_mono (show XB + u ≤ B by omega)
    have := toNat_size (x[u]'hlt)
    have hI1 := inv_wr hl hI (XB + u) (d := r.t1) (by simp [scr]) hD.pc_t1 hD.cap_t1 hD.cnt_t1
    have hI2 := inv_wr hl hI1 (S.mem (XB + u)) (d := r.t6) (by simp [scr]) hD.pc_t6 hD.cap_t6
      hD.cnt_t6
    have hz2 := hI2.z0 hl he
    refine ⟨_, _, WExec.no (by rw [hxl, hu]; exact h)
      (WExec.seq (wop (t := S.write r.t1 (XB + u)) (by simp only [Op.eval, hxb, hu]))
        (wop ?ev)), hI2, ?_, ?_, ?_⟩
    case ev =>
      simp only [Op.eval, write_mem_self, write_mem_ne _ _ (show XB + u ≠ r.t1 by omega)]
    · rw [write_mem_self, hI.inp hl he u hlt, List.getElem?_eq_getElem hlt]; rfl
    · rw [write_mem_ne _ _ hD.run_t6, write_mem_ne _ _ hD.run_t1]
    · simp only [jumpCost, Op.cost, hxl, hu, hxb, hz2, write_mem_self,
        write_mem_ne _ _ (show XB + u ≠ r.t1 by omega), hI.inp hl he u hlt, Nat.size_zero, write_mem_ne _ _ (Ne.symm hl.t6_nz), write_mem_ne _ _ (Ne.symm hl.t1_nz), hz]
      omega

theorem blk_coin_inner (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) {o : Option Bool} (h6 : S.mem r.t6 = bitVal o) :
    ∃ S' k, WExec τ J (.branch r.t6 r.zero .skip (.branch r.t6 r.one .skip
        (.op (.const r.t6 0)))) S S' k ∧
      Inv r B L S0 S' pc out mem work cnt ∧ S'.mem r.t6 = (o.getD false).toNat ∧
      S'.mem r.run = S.mem r.run ∧ k ≤ 12 * K + 4 * W := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have hzr := hI.zero hD hl he
  have h1 := hI.one hD hl he
  have hz := hI.z0 hl he
  have := size_two
  have := Nat.size_one
  rcases o with _ | _ | _
  · have hI2 := inv_wr hl hI 0 (d := r.t6) (by simp [scr]) hD.pc_t6 hD.cap_t6 hD.cnt_t6
    have hz2 := hI2.z0 hl he
    refine ⟨_, _, WExec.no (by rw [h6, hzr]; simp [bitVal])
      (WExec.no (by rw [h6, h1]; simp [bitVal]) (WExec.op _ _)), hI2, by simp [Op.eval], ?_, ?_⟩
    · exact write_mem_ne _ _ hD.run_t6
    · simp only [jumpCost, Op.cost, h6, hzr, h1, bitVal, Op.eval, hz2, Nat.size_zero]; omega
  · refine ⟨_, _, WExec.yes (by rw [h6, hzr]; simp [bitVal]) (WExec.skip _), hI,
      by rw [h6]; rfl, rfl, ?_⟩
    simp only [jumpCost, h6, hzr, bitVal, Bool.toNat_false, Nat.size_zero]; omega
  · refine ⟨_, _, WExec.no (by rw [h6, hzr]; simp [bitVal])
      (WExec.yes (by rw [h6, h1]; simp [bitVal]) (WExec.skip _)), hI, by rw [h6]; rfl, rfl, ?_⟩
    simp only [jumpCost, h6, hzr, h1, bitVal, Bool.toNat_true, hz, Nat.size_zero]; omega

theorem blk_coin (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) {u : ℕ} (hu : S.mem r.t5 = u)
    (hWc : (co + cl).size ≤ W) :
    ∃ S' k, WExec τ J (.branch r.cl r.t5 (.op (.const r.t6 2))
        (.seq (.op (.add r.t1 r.co r.t5)) (.seq (.op (.coin r.t6 r.t1))
          (.branch r.t6 r.zero .skip (.branch r.t6 r.one .skip (.op (.const r.t6 0))))))) S S' k ∧
      Inv r B L S0 S' pc out mem work cnt ∧
      S'.mem r.t6 = bitVal (windowCoins τ.coins co cl)[u]? ∧
      S'.mem r.run = S.mem r.run ∧ k ≤ 30 * K + 12 * W + 2 * u.size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have hcl := hI.vcl hD hl he
  have hco := hI.vco hD hl he
  have hz := hI.z0 hl he
  have := size_mono (show cl ≤ co + cl by omega)
  have := size_mono (show co ≤ co + cl by omega)
  have := size_two
  by_cases h : cl ≤ u
  · refine ⟨S.write r.t6 2, _, WExec.yes (by rw [hcl, hu]; exact h) (WExec.op _ _),
      inv_wr hl hI 2 (d := r.t6) (by simp [scr]) hD.pc_t6 hD.cap_t6 hD.cnt_t6,
      by rw [write_mem_self, windowCoins_get, if_neg (by omega)]; rfl,
      write_mem_ne _ _ hD.run_t6, ?_⟩
    simp only [jumpCost, Op.cost, hcl, hu]; omega
  · have := size_mono (show co + u ≤ co + cl by omega)
    have := bitVal_size τ.coins[co + u]?
    have hI1 := inv_wr hl hI (co + u) (d := r.t1) (by simp [scr]) hD.pc_t1 hD.cap_t1 hD.cnt_t1
    have hI2 := inv_wr hl hI1 (bitVal τ.coins[co + u]?) (d := r.t6) (by simp [scr]) hD.pc_t6
      hD.cap_t6 hD.cnt_t6
    obtain ⟨S3, k3, e3, hI3, h3, hr3, c3⟩ := blk_coin_inner (τ := τ) (J := J) hD hl he hI2
      (write_mem_self _ _ _)
    have hz3 := hI3.z0 hl he
    refine ⟨S3, _, WExec.no (by rw [hcl, hu]; exact h)
      (WExec.seq (wop (t := S.write r.t1 (co + u)) (by simp only [Op.eval, hco, hu]))
        (WExec.seq (wop (t := (S.write r.t1 (co + u)).write r.t6 (bitVal τ.coins[co + u]?))
          (by simp only [Op.eval, write_mem_self])) e3)), hI3, ?_, ?_, ?_⟩
    · rw [h3, windowCoins_get, if_pos (by omega)]; rfl
    · rw [hr3, write_mem_ne _ _ hD.run_t6, write_mem_ne _ _ hD.run_t1]
    · simp only [jumpCost, Op.cost, hcl, hu, hco, hz3, write_mem_self, Nat.size_zero]
      omega

theorem hd_readInput (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (p d a : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.readInput d a)) S S' k ∧
      Inv r B L S0 S' (p+1) out (Function.update mem d (bitVal x[mem a]?))
        (work + 1 + d.size + a.size + (mem a).size + (bitVal x[mem a]?).size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 40 * (K + W) + 10 * (1 + d.size + a.size + (mem a).size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  obtain ⟨S2, k2, e2, hI2, hv2, hr2, c2⟩ := blk_input (τ := τ) (J := J) hD hl he hI1 hv1
  have := bitVal_size x[mem a]?
  obtain ⟨S4, k4, e4, hI4, hr4, c4⟩ := tail_static (τ := τ) (J := J) hD hl he hI2 hroom
    (rv := r.t6) (by simp [IRegs.all]) hD.t6_t2 hD.t6_t4 hv2 d (p+1)
    (work + 1 + d.size + a.size + (mem a).size + (bitVal x[mem a]?).size) (by omega)
  refine ⟨S4, _, WExec.seq e1 (WExec.seq e2 e4), hI4, ?_, ?_⟩
  · rw [hr4, hr2, f1 _ hD.run_t1 hD.run_t5]
  · omega

theorem hd_readCoin (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hroom : L + cnt < B) (hWc : (co + cl).size ≤ W)
    (p d a : ℕ) :
    ∃ S' k, WExec τ J (handler r p (.readCoin d a)) S S' k ∧
      Inv r B L S0 S' (p+1) out
        (Function.update mem d (bitVal (windowCoins τ.coins co cl)[mem a]?))
        (work + 1 + d.size + a.size + (mem a).size +
          (bitVal (windowCoins τ.coins co cl)[mem a]?).size) (cnt+1) ∧
      S'.mem r.run = S.mem r.run ∧
      k ≤ 60 * (K + W) + 10 * (1 + d.size + a.size + (mem a).size) + (p+1).size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  obtain ⟨S1, k1, e1, hI1, hv1, f1, c1⟩ := rs_inv (τ := τ) (J := J) hD hl he hI (Or.inl rfl) a
  obtain ⟨S2, k2, e2, hI2, hv2, hr2, c2⟩ := blk_coin (τ := τ) (J := J) hD hl he hI1 hv1 hWc
  have := bitVal_size (windowCoins τ.coins co cl)[mem a]?
  obtain ⟨S4, k4, e4, hI4, hr4, c4⟩ := tail_static (τ := τ) (J := J) hD hl he hI2 hroom
    (rv := r.t6) (by simp [IRegs.all]) hD.t6_t2 hD.t6_t4 hv2 d (p+1)
    (work + 1 + d.size + a.size + (mem a).size +
      (bitVal (windowCoins τ.coins co cl)[mem a]?).size) (by omega)
  refine ⟨S4, _, WExec.seq e1 (WExec.seq e2 e4), hI4, ?_, ?_⟩
  · rw [hr4, hr2, f1 _ hD.run_t1 hD.run_t5]
  · omega

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpG.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

section
variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ} {x : List Bool} {co cl : ℕ}
  {S0 S : Store} {cnt : ℕ}

theorem step_sim (Q : Program) (hD : Dist r) (hl : Lay r B L XB K J W)
    (he : Env r B L XB x co cl S0) (hWc : (co + cl).size ≤ W) (hKp : Q.length.size ≤ K)
    {st : State} (hh : st.halted = false) {i : Instr} (hQ : Q[st.pc]? = some i)
    (hI : Inv r B L S0 S st.pc st.out st.mem st.work cnt) (hroom : L + cnt < B) :
    ∃ S' k cnt', WExec τ J (handler r st.pc i) S S' k ∧
      Inv r B L S0 S' (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).pc
        (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).out
        (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).mem
        (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).work cnt' ∧
      S'.mem r.run = (if (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).halted
        then 0 else S.mem r.run) ∧
      st.work < (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).work ∧
      k ≤ 70 * (K + W) +
        10 * ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).work - st.work) := by
  have hpc : st.pc < Q.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hQ; cases hQ
  have hps : (st.pc + 1).size ≤ K := (size_mono (show st.pc + 1 ≤ Q.length by omega)).trans hKp
  cases i with
  | const d c =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_const (τ := τ) (J := J) hD hl he hI hroom st.pc d c
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | add d a b =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_add (τ := τ) (J := J) hD hl he hI hroom st.pc d a b
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | monus d a b =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_monus (τ := τ) (J := J) hD hl he hI hroom st.pc d a b
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | load d a =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_load (τ := τ) (J := J) hD hl he hI hroom st.pc d a
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | store a b =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_store (τ := τ) (J := J) hD hl he hI hroom st.pc a b
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | jle a b tg =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_jle (τ := τ) (J := J) hD hl he hI st.pc a b tg
    refine ⟨S', k, cnt, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | inputLength d =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_inputLength (τ := τ) (J := J) hD hl he hI hroom st.pc d
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | readInput d a =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_readInput (τ := τ) (J := J) hD hl he hI hroom st.pc d a
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | readCoin d a =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_readCoin (τ := τ) (J := J) hD hl he hI hroom hWc
      st.pc d a
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | readWitness d =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_lit (τ := τ) (J := J) hD hl he hI hroom st.pc d 2
      (st.work + 1 + d.size + (2:ℕ).size) (by omega) (by omega)
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false,
        List.getElem?_nil, bitVal] <;>
      first | exact hI' | (rw [hr]) | omega
  | query d a b =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_lit (τ := τ) (J := J) hD hl he hI hroom st.pc d 0
      (st.work + 1 + d.size + a.size + b.size + (st.mem a).size + (st.mem b).size +
        (queryString st.mem (st.mem a) (st.mem b)).length + (0:ℕ).size) (by omega) (by omega)
    refine ⟨S', k, cnt + 1, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false, noOracle] <;>
      first | exact hI' | (rw [hr]) | omega
  | output a =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_output (τ := τ) (J := J) hD hl he hI st.pc a
    refine ⟨S', k, cnt, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false] <;>
      first | exact hI' | (rw [hr]) | omega
  | outputBot =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_halt (τ := τ) (J := J) hD hl hI
    refine ⟨S', k, cnt, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false, if_true] <;>
      first | exact hI' | exact hr | omega
  | halt =>
    obtain ⟨S', k, e, hI', hr, hk⟩ := hd_halt (τ := τ) (J := J) hD hl hI
    refine ⟨S', k, cnt, e, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Program.step, hh, hQ, State.write, Bool.false_eq_true, if_false, if_true] <;>
      first | exact hI' | exact hr | omega

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpH.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

theorem handlers_get (r : IRegs) : ∀ (Q : Program) (b i : ℕ),
    (handlers r b Q)[i]? = Q[i]?.map (handler r (b + i))
  | [], b, i => by simp [handlers]
  | q :: Q, b, 0 => by simp [handlers]
  | q :: Q, b, i + 1 => by
    simp only [handlers, List.getElem?_cons_succ]
    rw [handlers_get r Q (b + 1) i, show b + 1 + i = b + (i + 1) by omega]

theorem write_write (S : Store) (d v w : ℕ) : (S.write d v).write d w = S.write d w := by
  simp [Store.write, Function.update_idem]

theorem step_halted (Q : Program) (τ : Tapes) (s : State) (h : s.halted = true) :
    Q.step τ s = s := by simp [Program.step, h]

theorem step_stuck (Q : Program) (τ : Tapes) (s : State) (h : Q[s.pc]? = none) :
    Q.step τ s = s := by
  unfold Program.step; split_ifs <;> simp [h]

theorem step_work_le (Q : Program) (τ : Tapes) (s : State) : s.work ≤ (Q.step τ s).work := by
  unfold Program.step
  split
  · exact le_rfl
  · split <;> (try simp only [State.write]) <;> omega

theorem step_work_lt (Q : Program) (τ : Tapes) (s : State) (hh : s.halted = false) {i : Instr}
    (hQ : Q[s.pc]? = some i) : s.work < (Q.step τ s).work := by
  unfold Program.step
  rw [hh, hQ]
  cases i <;> simp only [State.write, Bool.false_eq_true, if_false] <;> omega

theorem iter_work_le (Q : Program) (τ : Tapes) : ∀ (m : ℕ) (s : State),
    s.work ≤ ((Q.step τ)^[m] s).work
  | 0, s => le_rfl
  | m + 1, s => by
    rw [Function.iterate_succ_apply]
    exact (step_work_le Q τ s).trans (iter_work_le Q τ m _)

theorem arith_step (N E a b k : ℕ) (hE : 1 ≤ E) (hab : a < b)
    (hk : k ≤ (6 * N + 80) * E + 10 * (b - a)) : k + (6 * N + 90) * E * a ≤ (6 * N + 90) * E * b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - a - 1, by omega⟩
  have h1 : (6 * N + 80) * E ≤ (6 * N + 80) * E * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 : 10 * (d + 1) ≤ 10 * E * (d + 1) := by nlinarith
  have : (6 * N + 90) * E * (a + 1 + d) =
      (6 * N + 90) * E * a + ((6 * N + 80) * E * (d + 1) + 10 * E * (d + 1)) := by ring
  have : a + 1 + d - a = d + 1 := by omega
  omega

section
variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ} {x : List Bool} {co cl : ℕ}
  {S0 S : Store} {cnt : ℕ}

theorem dispatch_sel {key ds : ℕ} (hk : key ≠ ds) (p k : ℕ) (c : Cmd) (S' : Store)
    (h0 : S'.mem 0 = 0) : ∀ (cs : List Cmd) (base : ℕ) (S : Store), base ≤ p →
    cs[p - base]? = some c → S.mem key = p → WExec τ J c (S.write ds p) S' k →
    WExec τ J (dispatch key ds base cs) S S'
      (k + (p - base + 1) * (3 + 2 * ds.size + key.size + 3 * p.size + 2 * J))
  | [], base, S, hb, hc, _, _ => by simp at hc
  | c' :: cs, base, S, hb, hc, hS, e => by
    by_cases hpb : p = base
    · subst hpb
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      refine WExec.mono (WExec.seq (WExec.op S (.const ds p))
        (WExec.yes (n := dispatch key ds (p + 1) cs) ?_ e)) ?_
      · simp only [Op.eval, write_mem_self, write_mem_ne _ _ hk, hS, le_refl]
      · simp only [Op.cost, jumpCost, Op.eval, write_mem_self, write_mem_ne _ _ hk, hS,
          Nat.sub_self, zero_add, one_mul]
        omega
    · have hb' : base + 1 ≤ p := by omega
      have hc' : cs[p - (base + 1)]? = some c := by
        rw [show p - base = (p - (base + 1)) + 1 by omega] at hc; simpa using hc
      have ih := dispatch_sel hk p k c S' h0 cs (base + 1) (S.write ds base) hb' hc'
        (by rw [write_mem_ne _ _ hk, hS]) (by rw [write_write]; exact e)
      refine WExec.mono (WExec.seq (WExec.op S (.const ds base)) (WExec.no (y := c') ?_ ih)) ?_
      · simp only [Op.eval, write_mem_self, write_mem_ne _ _ hk, hS]; omega
      · have := size_mono (show base ≤ p by omega)
        have hm : (p - base + 1) * (3 + 2 * ds.size + key.size + 3 * p.size + 2 * J) =
            (p - (base + 1) + 1) * (3 + 2 * ds.size + key.size + 3 * p.size + 2 * J) +
            (3 + 2 * ds.size + key.size + 3 * p.size + 2 * J) := by
          rw [show p - base + 1 = (p - (base + 1) + 1) + 1 by omega, Nat.succ_mul]
        simp only [Op.cost, jumpCost, Op.eval, write_mem_self, write_mem_ne _ _ hk, hS, h0,
          Nat.size_zero]
        omega

theorem iter_sim (Q : Program) (hD : Dist r) (hl : Lay r B L XB K J W)
    (he : Env r B L XB x co cl S0) (hWc : (co + cl).size ≤ W) (hKp : Q.length.size ≤ K)
    {st : State} (hh : st.halted = false) {i : Instr} (hQ : Q[st.pc]? = some i)
    (hI : Inv r B L S0 S st.pc st.out st.mem st.work cnt) (hroom : L + cnt < B) :
    ∃ S' k cnt', WExec τ J (dispatch r.pc r.ds 0 (handlers r 0 Q)) S S' k ∧
      Inv r B L S0 S' (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).pc
        (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).out
        (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).mem
        (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).work cnt' ∧
      S'.mem r.run = (if (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).halted
        then 0 else S.mem r.run) ∧
      st.work < (Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).work ∧
      k ≤ 76 * (K + W) + 6 * (Q.length * (K + W)) +
        10 * ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ st).work - st.work) := by
  have hpc : st.pc < Q.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hQ; cases hQ
  have hps : st.pc.size ≤ K := (size_mono (show st.pc ≤ Q.length by omega)).trans hKp
  have hI1 := inv_wr hl hI st.pc (d := r.ds) (by simp [scr]) hD.pc_ds hD.cap_ds hD.cnt_ds
  obtain ⟨S', k, cnt', e, hI', hr, hlt, hk⟩ := step_sim (τ := τ) (J := J) Q hD hl he hWc hKp hh hQ
    hI1 hroom
  have h0 := hI'.z0 hl he
  have hsel : (handlers r 0 Q)[st.pc - 0]? = some (handler r st.pc i) := by
    rw [handlers_get, Nat.sub_zero, hQ]; simp
  have ed := dispatch_sel (τ := τ) (J := J) hD.pc_ds st.pc k _ S' h0 (handlers r 0 Q) 0 S
    (Nat.zero_le _) hsel hI.hpc e
  refine ⟨S', _, cnt', ed, hI', by rw [hr, write_mem_ne _ _ hD.run_ds], hlt, ?_⟩
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have hm : (st.pc - 0 + 1) * (3 + 2 * r.ds.size + r.pc.size + 3 * st.pc.size + 2 * J) ≤
      Q.length * (6 * (K + W)) := Nat.mul_le_mul (by omega) (by omega)
  have : Q.length * (6 * (K + W)) = 6 * (Q.length * (K + W)) := by ring
  omega

theorem loop_sim (Q : Program) (hD : Dist r) (hl : Lay r B L XB K J W)
    (he : Env r B L XB x co cl S0) (hWc : (co + cl).size ≤ W) (hKp : Q.length.size ≤ K)
    (T : ℕ) (hT : L + T < B) : ∀ (n : ℕ) (st : State) (S : Store) (cnt : ℕ),
    st.halted = false →
    ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩)^[n] st).halted = true →
    ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩)^[n] st).work ≤ T →
    Inv r B L S0 S st.pc st.out st.mem st.work cnt → S.mem r.run = 1 →
    ∃ S' k cnt', WExec τ J (interp r Q) S S' k ∧
      Inv r B L S0 S' ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩)^[n] st).pc
        ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩)^[n] st).out
        ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩)^[n] st).mem
        ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩)^[n] st).work cnt' ∧
      S'.mem r.run = 0 ∧
      k + (6 * Q.length + 90) * (K + W) * st.work ≤
        (6 * Q.length + 90) * (K + W) *
          ((Q.step ⟨x, windowCoins τ.coins co cl, [], noOracle⟩)^[n] st).work +
        (6 * Q.length + 90) * (K + W)
  | 0, st, S, cnt, hh, hF, _, _, _ => by simp [hh] at hF
  | n + 1, st, S, cnt, hh, hF, hFT, hI, hrun => by
    rw [Function.iterate_succ_apply] at hF hFT ⊢
    set τQ : Tapes := ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ with hτQ
    obtain ⟨i, hQ⟩ : ∃ i, Q[st.pc]? = some i := by
      cases hq : Q[st.pc]? with
      | none =>
        rw [step_stuck Q τQ st hq, Function.iterate_fixed (step_stuck Q τQ st hq)] at hF
        rw [hh] at hF; cases hF
      | some i => exact ⟨i, rfl⟩
    have hw1 := iter_work_le Q τQ n (Q.step τQ st)
    have hw0 := step_work_lt Q τQ st hh hQ
    have hcw := hI.cost
    obtain ⟨S1, k1, cnt1, e1, hI1, hr1, hlt, hk1⟩ := iter_sim (τ := τ) (J := J) Q hD hl he hWc hKp
      hh hQ hI (by omega)
    rw [← hτQ] at hI1 hr1 hlt hk1
    have hz1 := hI1.z0 hl he
    have hzr := hI.zero hD hl he
    have hzr1 := hI1.zero hD hl he
    (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
    have hG : (6 * Q.length + 90) * (K + W) = 6 * (Q.length * (K + W)) + 90 * (K + W) := by ring
    have har := arith_step Q.length (K + W) st.work (Q.step τQ st).work
      (jumpCost J S r.run r.zero + k1 + jumpCost J S1 0 0) (by omega) hlt (by
        have : (6 * Q.length + 80) * (K + W) = 6 * (Q.length * (K + W)) + 80 * (K + W) := by ring
        simp only [jumpCost, hrun, hzr, hz1, Nat.size_zero, Nat.size_one]; omega)
    by_cases h1 : (Q.step τQ st).halted = true
    · rw [if_pos h1] at hr1
      rw [Function.iterate_fixed (step_halted Q τQ _ h1)] at hF hFT ⊢
      refine ⟨S1, _, cnt1, WExec.again (by rw [hrun, hzr]; omega) e1
        (WExec.done (by rw [hr1, hzr1])), hI1, hr1, ?_⟩
      have : jumpCost J S1 r.run r.zero ≤ 90 * (K + W) := by
        simp only [jumpCost, hr1, hzr1, Nat.size_zero]; omega
      omega
    · rw [if_neg h1, hrun] at hr1
      obtain ⟨S2, k2, cnt2, e2, hI2, hr2, hk2⟩ := loop_sim Q hD hl he hWc hKp T hT n
        (Q.step τQ st) S1 cnt1 (by simpa using h1) hF hFT hI1 hr1
      rw [← hτQ] at hI2
      refine ⟨S2, _, cnt2, WExec.again (by rw [hrun, hzr]; omega) e1 e2, hI2, hr2, ?_⟩
      rw [← hτQ] at hk2
      omega

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpI.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

def clearBody (r : IRegs) : Cmd :=
  .seq (.op (.add r.t1 r.logb r.t5)) (.seq (.op (.load r.t6 r.t1))
      (.seq (.op (.add r.t2 r.big r.t6)) (.seq (.op (.store r.t2 r.zero))
        (.seq (.op (.store r.t1 r.zero)) (.op (.add r.t5 r.t5 r.one))))))

theorem clear_eq (r : IRegs) :
    clear r = .seq (.op (.const r.t5 0)) (.seq (.whileGt r.cnt r.t5 (clearBody r))
      (.op (.const r.cnt 0))) := rfl

section
variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ}

theorem body_ok (hD : Dist r) (hl : Lay r B L XB K J W) (S : Store) {j c u : ℕ}
    (hj : j < c) (hc : L + c ≤ B) (h5 : S.mem r.t5 = j) (hL : S.mem r.logb = L)
    (hB : S.mem r.big = B) (hz : S.mem r.zero = 0) (h1 : S.mem r.one = 1)
    (hu : S.mem (L + j) = u) :
    ∃ k, WExec τ J (clearBody r) S
      ((((((S.write r.t1 (L + j)).write r.t6 u).write r.t2 (B + u)).write (B + u) 0).write
        (L + j) 0).write r.t5 (j + 1)) k ∧ k ≤ 15 * K + 10 * W + 4 * u.size := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have := size_add_le B u
  have := size_mono (show L ≤ B by omega)
  have := size_mono (show j ≤ B by omega)
  have := size_mono (show L + j ≤ B by omega)
  have := size_mono (show j + 1 ≤ B by omega)
  have := Nat.size_one
  refine ⟨_, WExec.seq (wop (t := S.write r.t1 (L + j)) ?e1)
    (WExec.seq (wop (t := (S.write r.t1 (L + j)).write r.t6 u) ?e2)
    (WExec.seq (wop (t := ((S.write r.t1 (L + j)).write r.t6 u).write r.t2 (B + u)) ?e3)
    (WExec.seq (wop (t := (((S.write r.t1 (L + j)).write r.t6 u).write r.t2 (B + u)).write
      (B + u) 0) ?e4)
    (WExec.seq (wop (t := ((((S.write r.t1 (L + j)).write r.t6 u).write r.t2 (B + u)).write
      (B + u) 0).write (L + j) 0) ?e5) (wop ?e6))))), ?_⟩
  case e1 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hL, h5]
  case e2 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hu]
  case e3 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hB]
  case e4 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hz]
  case e5 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hz]
  case e6 => simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, h5, h1]
  · simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out, hL, h5, hu, hB, hz, h1]; simp only [Nat.size_zero]; omega

theorem clear_loop (hD : Dist r) (hl : Lay r B L XB K J W) (c : ℕ) (lg : ℕ → ℕ)
    (hcB : L + c ≤ B) : ∀ (m j : ℕ) (S : Store), c - j = m → j ≤ c → S.mem r.t5 = j →
    S.mem r.cnt = c → S.mem r.logb = L → S.mem r.big = B → S.mem r.zero = 0 →
    S.mem r.one = 1 → S.mem 0 = 0 →
    (∀ j', j ≤ j' → j' < c → S.mem (L + j') = lg j') →
    (∀ u, S.mem (u + B) ≠ 0 → ∃ j', j ≤ j' ∧ j' < c ∧ lg j' = u) →
    ∃ S' k, WExec τ J (.whileGt r.cnt r.t5 (clearBody r)) S S' k ∧ S'.out = S.out ∧
      (∀ u, S'.mem (u + B) = 0) ∧ (∀ j', j ≤ j' → j' < c → S'.mem (L + j') = 0) ∧
      (∀ y, y ≠ r.t1 → y ≠ r.t2 → y ≠ r.t5 → y ≠ r.t6 → y < B → (y < L + j ∨ L + c ≤ y) →
        S'.mem y = S.mem y) ∧
      k + ∑ i ∈ Finset.range j, (20 * (K + W) + 4 * (lg i).size) ≤
        ∑ i ∈ Finset.range c, (20 * (K + W) + 4 * (lg i).size) + 20 * (K + W) := by
  intro m
  induction m with
  | zero =>
    intro j S hm hj h5 hc hL hB hz h1 h0 hlog hpend
    have hjc : j = c := by omega
    subst hjc
    (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
    have := size_mono (show j ≤ B by omega)
    refine ⟨S, _, WExec.done (by rw [hc, h5]), rfl, fun u => ?_, fun j' h1 h2 => by omega,
      fun y _ _ _ _ _ _ => rfl, ?_⟩
    · by_contra hne
      obtain ⟨j', h1, h2, _⟩ := hpend u hne
      omega
    · simp only [jumpCost, hc, h5]; omega
  | succ m ih =>
    intro j S hm hj h5 hc hL hB hz h1 h0 hlog hpend
    have hjc : j < c := by omega
    (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
    obtain ⟨kb, eb, hkb⟩ := body_ok (τ := τ) (J := J) hD hl S hjc hcB h5 hL hB hz h1
      (hlog j le_rfl hjc)
    set u := lg j with hu
    set S1 := (((((S.write r.t1 (L + j)).write r.t6 u).write r.t2 (B + u)).write (B + u) 0).write
        (L + j) 0).write r.t5 (j + 1) with hS1
    have hf1 : ∀ y, y ≠ r.t1 → y ≠ r.t2 → y ≠ r.t5 → y ≠ r.t6 → y ≠ B + u → y ≠ L + j →
        S1.mem y = S.mem y := by
      intro y a1 a2 a5 a6 ab al
      rw [hS1]; simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
    have hreg : ∀ y, y < XB → y ≠ r.t1 → y ≠ r.t2 → y ≠ r.t5 → y ≠ r.t6 →
        S1.mem y = S.mem y := fun y hy a1 a2 a5 a6 => hf1 y a1 a2 a5 a6 (by omega) (by omega)
    have hz1 : S1.mem 0 = 0 := by
      rw [hreg 0 (by omega) (Ne.symm hl.t1_nz) (Ne.symm hl.t2_nz) (Ne.symm hl.t5_nz)
        (Ne.symm hl.t6_nz), h0]
    obtain ⟨S', k', e', ho', hsim', hlog', hfr', hk'⟩ := ih (j + 1) S1 (by omega) (by omega)
      (by rw [hS1]; simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out])
      (by rw [hreg _ hl.cnt_lt hD.cnt_t1 hD.cnt_t2 hD.cnt_t5 hD.cnt_t6, hc])
      (by rw [hreg _ hl.logb_lt hD.logb_t1 hD.logb_t2 hD.logb_t5 hD.logb_t6, hL])
      (by rw [hreg _ hl.big_lt hD.big_t1 hD.big_t2 hD.big_t5 hD.big_t6, hB])
      (by rw [hreg _ hl.zero_lt hD.zero_t1 hD.zero_t2 hD.zero_t5 hD.zero_t6, hz])
      (by rw [hreg _ hl.one_lt hD.one_t1 hD.one_t2 hD.one_t5 hD.one_t6, h1]) hz1
      (fun j' a b => by
        rw [hf1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          hlog j' (by omega) b])
      (fun w hw => by
        have hwu : w ≠ u := by
          rintro rfl
          apply hw; rw [hS1, show u + B = B + u from add_comm _ _]; simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
        rw [hf1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)] at hw
        obtain ⟨j', a, b, c'⟩ := hpend w hw
        refine ⟨j', ?_, b, c'⟩
        rcases Nat.eq_or_lt_of_le a with h | h
        · subst h; exact absurd (c'.symm.trans hu.symm) hwu
        · omega)
    refine ⟨S', _, WExec.again (by rw [hc, h5]; omega) eb e', ho'.trans (by rw [hS1]; rfl),
      hsim', fun j' a b => ?_, fun y a1 a2 a5 a6 hyB hy => ?_, ?_⟩
    · rcases Nat.eq_or_lt_of_le a with h | h
      · subst h
        rw [hfr' _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hS1]
        simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]
      · exact hlog' j' (by omega) b
    · rw [hfr' y a1 a2 a5 a6 hyB (by omega), hf1 y a1 a2 a5 a6 (by omega) (by omega)]
    · rw [Finset.sum_range_succ] at hk'
      have := size_mono (show c ≤ B by omega)
      have := size_mono (show j ≤ B by omega)
      simp only [jumpCost, hc, h5, hz1, Nat.size_zero]
      rw [← hu] at hk'
      omega

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpJ.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

section
variable {τ : Tapes} {J : ℕ} {r : IRegs} {B L XB K W : ℕ} {x : List Bool} {co cl : ℕ}
  {S0 S : Store} {pc : ℕ} {out : List Bool} {mem : ℕ → ℕ} {work cnt : ℕ}

theorem sum_split (c E : ℕ) (g : ℕ → ℕ) :
    ∑ i ∈ Finset.range c, (E + 4 * g i) = c * E + 4 * ∑ i ∈ Finset.range c, g i := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, Finset.mul_sum]

theorem clear_ok (hD : Dist r) (hl : Lay r B L XB K J W) (he : Env r B L XB x co cl S0)
    (hI : Inv r B L S0 S pc out mem work cnt) (hcB : L + cnt ≤ B) :
    ∃ S' k, WExec τ J (clear r) S S' k ∧ S'.out = S.out ∧ (∀ u, S'.mem (u + B) = 0) ∧
      (∀ j < cnt, S'.mem (L + j) = 0) ∧ S'.mem r.cnt = 0 ∧
      (∀ y, y ≠ r.t1 → y ≠ r.t2 → y ≠ r.t5 → y ≠ r.t6 → y ≠ r.cnt → y < B →
        (y < L ∨ L + cnt ≤ y) → S'.mem y = S.mem y) ∧
      k ≤ work * (20 * (K + W)) + 4 * work + 22 * (K + W) := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  have hreg : ∀ y, y < XB → y ≠ r.t5 → (S.write r.t5 0).mem y = S.mem y :=
    fun y _ h => write_mem_ne _ _ h
  obtain ⟨S2, k2, e2, o2, hsim2, hlog2, hfr2, hk2⟩ := clear_loop (τ := τ) (J := J) hD hl cnt
    (fun j => S.mem (L + j)) hcB cnt 0 (S.write r.t5 0) (by omega) (by omega)
    (write_mem_self _ _ _)
    (by rw [hreg _ hl.cnt_lt hD.cnt_t5, hI.hcnt])
    (by rw [hreg _ hl.logb_lt hD.logb_t5, hI.logb hD hl he])
    (by rw [hreg _ hl.big_lt hD.big_t5, hI.big hD hl he])
    (by rw [hreg _ hl.zero_lt hD.zero_t5, hI.zero hD hl he])
    (by rw [hreg _ hl.one_lt hD.one_t5, hI.one hD hl he])
    (by rw [hreg _ (by omega) (Ne.symm hl.t5_nz), hI.z0 hl he])
    (fun j' _ _ => write_mem_ne _ _ (by omega))
    (fun u hu => by
      rw [write_mem_ne _ _ (by omega), hI.sim] at hu
      obtain ⟨j, hj, e⟩ := hI.logged u hu
      exact ⟨j, by omega, hj, e⟩)
  refine ⟨S2.write r.cnt 0, _, by
      rw [clear_eq]; exact WExec.seq (WExec.op _ _) (WExec.seq e2 (WExec.op _ _)),
    by rw [write_out, o2]; rfl, fun u => by rw [write_mem_ne _ _ (by omega), hsim2],
    fun j hj => by rw [write_mem_ne _ _ (by omega), hlog2 j (by omega) hj],
    write_mem_self _ _ _, fun y a1 a2 a5 a6 ac hyB hy => ?_, ?_⟩
  · rw [write_mem_ne _ _ ac, hfr2 y a1 a2 a5 a6 hyB (by omega), write_mem_ne _ _ a5]
  · have hc := hI.cost
    simp only [Finset.range_zero, Finset.sum_empty, add_zero] at hk2
    rw [sum_split] at hk2
    have := Nat.mul_le_mul_right (20 * (K + W)) (show cnt ≤ work by omega)
    simp only [Op.cost, Nat.size_zero]
    omega

theorem resets_ok (hl : Lay r B L XB K J W) (s : Store) :
    ∃ k, WExec τ J (resets r) s ((((((((s.write r.pc 0).write r.ds 0).write r.t1 0).write r.t2 0).write
      r.t3 0).write r.t4 0).write r.t5 0).write r.t6 0) k ∧ k ≤ 8 + 8 * K := by
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  refine ⟨_, WExec.seq (WExec.op _ _) (WExec.seq (WExec.op _ _) (WExec.seq (WExec.op _ _)
    (WExec.seq (WExec.op _ _) (WExec.seq (WExec.op _ _) (WExec.seq (WExec.op _ _)
    (WExec.seq (WExec.op _ _) (WExec.op _ _))))))), ?_⟩
  simp only [Op.cost, Nat.size_zero]; omega

theorem resets_ne (s : Store) {y : ℕ} (h1 : y ≠ r.pc) (h2 : y ≠ r.ds) (h3 : y ≠ r.t1)
    (h4 : y ≠ r.t2) (h5 : y ≠ r.t3) (h6 : y ≠ r.t4) (h7 : y ≠ r.t5) (h8 : y ≠ r.t6) :
    ((((((((s.write r.pc 0).write r.ds 0).write r.t1 0).write r.t2 0).write
      r.t3 0).write r.t4 0).write r.t5 0).write r.t6 0).mem y = s.mem y := by
  rw [write_mem_ne _ _ h8, write_mem_ne _ _ h7, write_mem_ne _ _ h6, write_mem_ne _ _ h5,
    write_mem_ne _ _ h4, write_mem_ne _ _ h3, write_mem_ne _ _ h2, write_mem_ne _ _ h1]

theorem resets_zero (hD : Dist r) (s : Store) {y : ℕ}
    (hy : y = r.pc ∨ y = r.ds ∨ y = r.t1 ∨ y = r.t2 ∨ y = r.t3 ∨ y = r.t4 ∨ y = r.t5 ∨ y = r.t6) :
    ((((((((s.write r.pc 0).write r.ds 0).write r.t1 0).write r.t2 0).write
      r.t3 0).write r.t4 0).write r.t5 0).write r.t6 0).mem y = 0 := by
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (disch := (first | assumption | omega | with_reducible (have hD__ := ‹Dist _›; cases hD__; assumption))) only [Op.eval, Op.cost, jumpCost, write_mem_self, write_mem_ne, write_out]

end

end TargetedSamplers.Structured.InterpPf


-- ===== Solutions/Dev/InterpProof.lean =====

set_option autoImplicit false

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp

namespace TargetedSamplers.Structured.InterpPf

theorem final_cost (N K W T w k1 k2 k3 : ℕ) (hK : 1 ≤ K) (hW : 1 ≤ W) (hw : w ≤ T)
    (hk1 : k1 ≤ (6 * N + 90) * (K + W) * w + (6 * N + 90) * (K + W))
    (hk2 : k2 ≤ w * (20 * (K + W)) + 4 * w + 22 * (K + W)) (hk3 : k3 ≤ 8 + 8 * K) :
    k1 + (k2 + k3) ≤ (6 * N + 200) * (K + 1) * (T + 1) * W := by
  have e1 : (6 * N + 90) * (K + W) * w ≤ (6 * N + 90) * (K + W) * T :=
    Nat.mul_le_mul_left _ hw
  have e2 : w * (20 * (K + W)) ≤ T * (20 * (K + W)) := Nat.mul_le_mul_right _ hw
  have e3 : K + W ≤ (K + 1) * W := by nlinarith
  have e4 : (6 * N + 200) * (K + W) * (T + 1) ≤ (6 * N + 200) * ((K + 1) * W) * (T + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ e3)
  have e5 : T ≤ (K + W) * T := Nat.le_mul_of_pos_left _ (by omega)
  have : (6 * N + 200) * ((K + 1) * W) * (T + 1) = (6 * N + 200) * (K + 1) * (T + 1) * W := by
    ring
  have : (6 * N + 200) * (K + W) * (T + 1) =
      (6 * N + 90) * (K + W) * T + (6 * N + 90) * (K + W) + 110 * ((K + W) * T) +
        110 * (K + W) := by ring
  have : T * (20 * (K + W)) = 20 * ((K + W) * T) := by ring
  have : (6 * N + 90) * (K + W) = 6 * (N * (K + W)) + 90 * (K + W) := by ring
  omega

end TargetedSamplers.Structured.InterpPf

open TargetedSamplers TargetedSamplers.Structured TargetedSamplers.Structured.Work
open TargetedSamplers.Structured.Interp
open TargetedSamplers.Structured.InterpPf

theorem solution (Q : Program) (r : IRegs) (hr : r.all.Nodup)
    (h0 : ∀ y ∈ r.all, y ≠ 0) :
    ∃ C : ℕ, ∀ (τ : Tapes) (J : ℕ) (x : List Bool) (co cl T BIG LOG XB : ℕ) (st : State) (S : Store),
      Q.final ⟨x, windowCoins τ.coins co cl, [], noOracle⟩ = some st → st.work ≤ T →
      Cmd.FieldsFit J (call r Q) →
      S.mem r.pc = 0 → S.mem r.run = 1 → S.mem r.cnt = 0 → S.mem r.cap = 2 → S.mem r.one = 1 →
      S.mem r.zero = 0 → S.mem r.ds = 0 → S.mem r.t1 = 0 → S.mem r.t2 = 0 → S.mem r.t3 = 0 →
      S.mem r.t4 = 0 → S.mem r.t5 = 0 → S.mem r.t6 = 0 → S.mem 0 = 0 →
      S.mem r.big = BIG → S.mem r.logb = LOG → S.mem r.xb = XB → S.mem r.xlen = x.length →
      S.mem r.co = co → S.mem r.cl = cl →
      (∀ y ∈ r.all, y < XB) → XB + x.length ≤ LOG → LOG + T + 1 ≤ BIG →
      (∀ i (hi : i < x.length), S.mem (XB + i) = (x[i]'hi).toNat) →
      (∀ u, S.mem (BIG + u) = 0) → (∀ j, j ≤ T → S.mem (LOG + j) = 0) →
      ∃ S' k, WExec τ J (call r Q) S S' k ∧ k ≤ C * (T + 1) * ((BIG + co + cl).size + J + 1) ∧
        S'.mem r.cap = capValue st.out ∧ S'.mem r.run = 0 ∧ S'.out = S.out ∧
        ∀ y, y ≠ r.cap → y ≠ r.run → S'.mem y = S.mem y := by
  have hD := Dist.of hr
  refine ⟨(6 * Q.length + 200) * ((r.all.map Nat.size).sum + Q.length.size + 1 + 1), ?_⟩
  intro τ J x co cl T BIG LOG XB st S hst hT _ hpc hrun hcnt hcap hone hzero hds ht1 ht2 ht3 ht4
    ht5 ht6 hz0 hbig hlogb hxb hxlen hco hcl hlt hxin hLB hinp hsim hlog
  have hsz : ∀ y ∈ r.all, y.size ≤ (r.all.map Nat.size).sum + Q.length.size + 1 := fun y hy => by
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := Nat.size) hy)
    omega
  have hl : Lay r BIG LOG XB ((r.all.map Nat.size).sum + Q.length.size + 1) J
      ((BIG + co + cl).size + J + 1) :=
    { lt := hlt, nz := h0, sz := hsz, xl := by omega, lb := by omega,
      wb := by have := size_mono (show BIG ≤ BIG + co + cl by omega); omega,
      k1 := by omega }
  have he : Env r BIG LOG XB x co cl S :=
    { big := hbig, logb := hlogb, xb := hxb, xlen := hxlen, co := hco, cl := hcl, one := hone,
      zero := hzero, z0 := hz0, inp := hinp, xin := hxin }
  have hWc : (co + cl).size ≤ (BIG + co + cl).size + J + 1 := by
    have := size_mono (show co + cl ≤ BIG + co + cl by omega); omega
  have hKp : Q.length.size ≤ (r.all.map Nat.size).sum + Q.length.size + 1 := by omega
  unfold Program.final at hst
  split_ifs at hst with hex
  cases hst
  unfold Program.config at hT
  have hI0 : Inv r BIG LOG S S State.init.pc State.init.out State.init.mem State.init.work 0 :=
    { hpc := hpc, hcap := hcap, hcnt := hcnt, sim := fun u => by rw [add_comm]; exact hsim u,
      logged := fun u hu => absurd rfl hu, cost := by simp [State.init],
      frame := fun _ _ _ => rfl, hout := rfl }
  obtain ⟨S1, k1, cnt1, e1, hI1, hr1, hk1⟩ := (fun hF => loop_sim (τ := τ) (J := J) Q hD hl he hWc
    hKp T (by omega) _ State.init S 0 rfl hF hT hI0 hrun) (by exact Nat.find_spec hex)
  have hcost1 := hI1.cost
  obtain ⟨S2, k2, e2, o2, hsim2, hlog2, hcnt2, hfr2, hk2⟩ := clear_ok (τ := τ) (J := J) hD hl he
    hI1 (by omega)
  obtain ⟨k3, e3, hk3⟩ := resets_ok (τ := τ) (J := J) hl S2
  (have := Lay.pc_lt hl; have := Lay.pc_sz hl; have := Lay.run_lt hl; have := Lay.run_sz hl; have := Lay.big_lt hl; have := Lay.big_sz hl; have := Lay.logb_lt hl; have := Lay.logb_sz hl; have := Lay.cnt_lt hl; have := Lay.cnt_sz hl; have := Lay.xb_lt hl; have := Lay.xb_sz hl; have := Lay.xlen_lt hl; have := Lay.xlen_sz hl; have := Lay.co_lt hl; have := Lay.co_sz hl; have := Lay.cl_lt hl; have := Lay.cl_sz hl; have := Lay.cap_lt hl; have := Lay.cap_sz hl; have := Lay.one_lt hl; have := Lay.one_sz hl; have := Lay.zero_lt hl; have := Lay.zero_sz hl; have := Lay.ds_lt hl; have := Lay.ds_sz hl; have := Lay.t1_lt hl; have := Lay.t1_sz hl; have := Lay.t2_lt hl; have := Lay.t2_sz hl; have := Lay.t3_lt hl; have := Lay.t3_sz hl; have := Lay.t4_lt hl; have := Lay.t4_sz hl; have := Lay.t5_lt hl; have := Lay.t5_sz hl; have := Lay.t6_lt hl; have := Lay.t6_sz hl; have := Lay.xl hl; have := Lay.lb hl; have := Lay.wb hl; have := Lay.k1 hl)
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 e3), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.init, Nat.mul_zero, add_zero] at hk1
    exact final_cost _ _ _ _ _ _ _ _ (by omega) (by omega) hT hk1 hk2 hk3
  · rw [resets_ne _ hD.cap_pc hD.cap_ds hD.cap_t1 hD.cap_t2 hD.cap_t3 hD.cap_t4 hD.cap_t5 hD.cap_t6,
      hfr2 _ hD.cap_t1 hD.cap_t2 hD.cap_t5 hD.cap_t6 hD.cap_cnt (by omega) (Or.inl (by omega)),
      hI1.hcap]
    rfl
  · rw [resets_ne _ hD.run_pc hD.run_ds hD.run_t1 hD.run_t2 hD.run_t3 hD.run_t4 hD.run_t5 hD.run_t6,
      hfr2 _ hD.run_t1 hD.run_t2 hD.run_t5 hD.run_t6 hD.run_cnt (by omega) (Or.inl (by omega)),
      hr1]
  · simp only [write_out]; rw [o2, hI1.hout]
  · intro y hycap hyrun
    by_cases hin : y = r.pc ∨ y = r.ds ∨ y = r.t1 ∨ y = r.t2 ∨ y = r.t3 ∨ y = r.t4 ∨ y = r.t5 ∨
        y = r.t6
    · rw [resets_zero hD _ hin]
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> symm <;> assumption
    simp only [not_or] at hin
    obtain ⟨ypc, yds, y1, y2, y3, y4, y5, y6⟩ := hin
    rw [resets_ne _ ypc yds y1 y2 y3 y4 y5 y6]
    by_cases ycnt : y = r.cnt
    · subst ycnt; rw [hcnt2, hcnt]
    have hys : y ∉ scr r := by
      simp only [scr, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨ypc, hyrun, hycap, ycnt, yds, y1, y2, y3, y4, y5, y6⟩
    by_cases hyB : BIG ≤ y
    · obtain ⟨u, rfl⟩ : ∃ u, y = BIG + u := ⟨y - BIG, by omega⟩
      rw [add_comm, hsim2, add_comm, hsim]
    by_cases hyl : LOG ≤ y ∧ y < LOG + cnt1
    · obtain ⟨j, rfl⟩ : ∃ j, y = LOG + j := ⟨y - LOG, by omega⟩
      rw [hlog2 j (by omega), hlog j (by omega)]
    · rw [hfr2 y y1 y2 y5 y6 ycnt (by omega) (by omega), hI1.frame y hys (by omega)]
