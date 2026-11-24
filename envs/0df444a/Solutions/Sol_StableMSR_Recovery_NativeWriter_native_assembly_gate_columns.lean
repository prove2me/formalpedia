-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.native_assembly_gate_columns
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T22:40:34.112862+00:00
-- url     : https://prove2.me/submissions/5de1f45a-3bfc-4355-aef8-d3ea875d3145
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_SingleRAM_global_assembly_resource_bound
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Relative_native_relative_relocation_pass
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Relative_native_unrelocated_region_reports
set_option linter.all false
namespace StableMSR.Recovery.NativeWriter.Relative
open OracleQueries Compiler SingleCircuit SingleCodes SingleRAM WindowCSP
open WindowProfiles (keys piece)
open scoped Classical
set_option autoImplicit false
def resolve (base token : ℤ) : ℤ := if 0≤token then base+token else -1-token
theorem raw_succ (x : World) (h w r : ℕ) :
    rawAssembly x h w (r+1)=appendRegion x h w r (rawAssembly x h w r) := by
  simp [rawAssembly,List.range_succ]

theorem append_fields (x : World) (h w r : ℕ) (a : Assembly) :
    (appendRegion x h w r a).gates = a.gates ++ (packet x h w r).gates.map (relocateGate a.gates.size) ∧
    ((appendRegion x h w r a).roots r:ℤ)=resolve a.gates.size (packet x h w r).token ∧
    ∀ i, i≠r → (appendRegion x h w r a).roots i=a.roots i := by
  by_cases key:r%x.n∈keys x (r/x.n)
  · by_cases pos:0<scale x (r/x.n)
    · simp [appendRegion,packet,key,pos,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..
    · simp [appendRegion,packet,key,pos,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..
  · simp [appendRegion,packet,key,resolve,Function.update_of_ne] <;> exact fun i hi=>Function.update_of_ne hi ..

theorem raw_size (x : World) (h w r : ℕ) : (rawAssembly x h w r).gates.size=firstGate x h w r := by
  induction r with
  | zero=>rfl
  | succ r ih=>rw [raw_succ,(append_fields ..).1,Array.size_append,Array.size_map,ih,firstGate]

theorem total_size (x : World) (h w : ℕ) : (globalAssembly x h w).gates.size=total x h w := by
  unfold globalAssembly padAssembly total
  simp only [Array.size_append,Array.size_replicate,raw_size]; omega

end StableMSR.Recovery.NativeWriter.Relative
namespace StableMSR.Recovery.NativeWriter.Relative
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
set_option autoImplicit false

theorem columns_of_reports
    (resources : ∀ (x : World) (e : ℚ), 0<e → e<1 → 2≤x.n →
      let G:=(globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
      82+42*G+7*(G*x.n)≤256*x.cap^3*x.n^(75*parameterEnvelope (e:ℝ)))
    (pass : ∃cmd : Cmd, ∀(x : World) (h w : ℕ) (s : Store), Reports x h w s →
      ∃t z, Executes x.dist cmd s t z ∧ z≤17+75*total x h w ∧
        let a:=globalAssembly x h w
        Columns x.n x.k x.rows a.gates a.roots t)
    (source : ∃c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd : Cmd, GeneratesReports e c D b cmd) :
    ∃c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd : Cmd, GeneratesColumns e c D b cmd := by
  obtain ⟨c,D,b,gen⟩:=source
  obtain ⟨rel,correct⟩:=pass
  refine ⟨c+512,D+3,b+75,?_⟩
  intro e he hl
  obtain ⟨src,make⟩:=gen e he hl
  refine ⟨.seq src rel,?_⟩
  intro x s hk kn met ready
  obtain ⟨u,z,go,work,raw⟩:=make x s hk kn met ready
  obtain ⟨v,f,run,tm,done⟩:=correct x (budget (e:ℝ)) (widthBound (e:ℝ)) u raw
  let E:=parameterEnvelope (e:ℝ)
  let A:=x.n^(75*E)
  let G:=(globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
  have lim : 82+42*G+7*(G*x.n)≤256*(x.cap^3*A) := by
    simpa only [Nat.mul_assoc] using resources x e he hl (by omega)
  have small : f≤17+75*G := by rwa [← total_size] at tm
  have ft : f≤512*(x.cap^3*A) := by omega
  let L:=x.cap^(D+3)*x.n^((b+75)*E)
  have cp:1≤x.cap:=by dsimp [World.cap];omega
  have lift (d t : ℕ) (hd : d≤D+3) (ht : t≤b+75) : x.cap^d*x.n^(t*E) ≤ L :=
    Nat.mul_le_mul (Nat.pow_le_pow_right cp hd) (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ ht))
  have z0 : z≤c*L:=work.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left c (lift D b (by omega) (by omega)))
  have f0 : f≤512*L:=ft.trans (Nat.mul_le_mul_left 512 (lift 3 75 (by omega) (by omega)))
  refine ⟨v,z+f,.seq go run,?_,done⟩
  change z+f≤(c+512)*x.cap^(D+3)*x.n^((b+75)*E)
  rw [Nat.mul_assoc,Nat.add_mul]
  exact Nat.add_le_add z0 f0

end StableMSR.Recovery.NativeWriter.Relative

open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.SingleRAM StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative
theorem solution :
    ∃ c D b : ℕ, ∀ e : ℚ, 0 < e → e < 1 → ∃ cmd : Cmd, GeneratesColumns e c D b cmd := by
  apply StableMSR.Recovery.NativeWriter.Relative.columns_of_reports _ native_relative_relocation_pass native_unrelocated_region_reports
  intro x e he hl hn
  exact (global_assembly_resource_bound x e he hl hn).2.2
