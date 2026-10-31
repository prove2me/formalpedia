-- Prove2me | solution 1 for OddGoldbach19.table_block8000_4
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T19:47:44.519982+00:00
-- url     : https://prove2.me/submissions/6f0b27f1-c196-4d05-aa71-a9e70e431512

import Definitions.Def_OddGoldbach19_CertificateData8000
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
namespace OddGoldbach19.Cert8000
theorem table_400 : ∀ j : Fin 100, WC (j.val+40000)≤WP (j.val+40000) := by decide +kernel
theorem table_401 : ∀ j : Fin 100, WC (j.val+40100)≤WP (j.val+40100) := by decide +kernel
theorem table_402 : ∀ j : Fin 100, WC (j.val+40200)≤WP (j.val+40200) := by decide +kernel
theorem table_403 : ∀ j : Fin 100, WC (j.val+40300)≤WP (j.val+40300) := by decide +kernel
theorem table_404 : ∀ j : Fin 100, WC (j.val+40400)≤WP (j.val+40400) := by decide +kernel
theorem table_405 : ∀ j : Fin 100, WC (j.val+40500)≤WP (j.val+40500) := by decide +kernel
theorem table_406 : ∀ j : Fin 100, WC (j.val+40600)≤WP (j.val+40600) := by decide +kernel
theorem table_407 : ∀ j : Fin 100, WC (j.val+40700)≤WP (j.val+40700) := by decide +kernel
theorem table_408 : ∀ j : Fin 100, WC (j.val+40800)≤WP (j.val+40800) := by decide +kernel
theorem table_409 : ∀ j : Fin 9, WC (j.val+40900)≤WP (j.val+40900) := by decide +kernel
end OddGoldbach19.Cert8000
open OddGoldbach19.Cert8000
theorem solution (d : ℕ) (hlo : 40000≤d) (hhi : d<40909) :
    OddGoldbach19.Cert8000.WC d≤OddGoldbach19.Cert8000.WP d := by
  have heq := Nat.mod_add_div d 100
  have hmod : d%100<100 := Nat.mod_lt _ (by norm_num)
  have hlow : 400≤d/100 := by omega
  have hupp : d/100≤409 := by omega
  generalize hK : d/100=k at *
  interval_cases k
  · have hh := table_400 ⟨d%100,hmod⟩
    have he : d%100+40000=d := by omega
    change WC (d%100+40000)≤WP (d%100+40000) at hh
    rwa [he] at hh
  · have hh := table_401 ⟨d%100,hmod⟩
    have he : d%100+40100=d := by omega
    change WC (d%100+40100)≤WP (d%100+40100) at hh
    rwa [he] at hh
  · have hh := table_402 ⟨d%100,hmod⟩
    have he : d%100+40200=d := by omega
    change WC (d%100+40200)≤WP (d%100+40200) at hh
    rwa [he] at hh
  · have hh := table_403 ⟨d%100,hmod⟩
    have he : d%100+40300=d := by omega
    change WC (d%100+40300)≤WP (d%100+40300) at hh
    rwa [he] at hh
  · have hh := table_404 ⟨d%100,hmod⟩
    have he : d%100+40400=d := by omega
    change WC (d%100+40400)≤WP (d%100+40400) at hh
    rwa [he] at hh
  · have hh := table_405 ⟨d%100,hmod⟩
    have he : d%100+40500=d := by omega
    change WC (d%100+40500)≤WP (d%100+40500) at hh
    rwa [he] at hh
  · have hh := table_406 ⟨d%100,hmod⟩
    have he : d%100+40600=d := by omega
    change WC (d%100+40600)≤WP (d%100+40600) at hh
    rwa [he] at hh
  · have hh := table_407 ⟨d%100,hmod⟩
    have he : d%100+40700=d := by omega
    change WC (d%100+40700)≤WP (d%100+40700) at hh
    rwa [he] at hh
  · have hh := table_408 ⟨d%100,hmod⟩
    have he : d%100+40800=d := by omega
    change WC (d%100+40800)≤WP (d%100+40800) at hh
    rwa [he] at hh
  · have hh := table_409 ⟨d%100,by omega⟩
    have he : d%100+40900=d := by omega
    change WC (d%100+40900)≤WP (d%100+40900) at hh
    rwa [he] at hh
#print axioms solution
