-- Prove2me | solution 1 for TuranMatching.ColorCritical.small_X_lt_gNum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:36:01.362673+00:00
-- url     : https://prove2.me/submissions/a2378d4d-ac79-4720-996d-23955bef7ec0

import Mathlib
import Definitions.Def_TuranMatching_ColorCritical_Setting

set_option autoImplicit false
open Finset SimpleGraph

namespace TMCAux

lemma gNum_ge (n k s : ℕ) (hk : 2 ≤ k) (hsn : s < n) :
    s * (n - s) ≤ TuranMatching.Clique.gNum n k s := by
  classical
  have hn : s ≤ n := hsn.le
  let a : Fin n := ⟨s, hsn⟩
  let A : Finset (Fin n) := Finset.Iio a
  let B : Finset (Fin n) := Finset.Ici a
  have hA : #A = s := by simp [A, a]
  have hB : #B = n - s := by simp [B, a]
  have hcls : ∀ v w : Fin n, v ∈ A → w ∈ B → (TuranMatching.Clique.bigGraph n k s).Adj v w := by
    intro v w hv hw
    have hv' : (v : ℕ) < s := Fin.lt_def.mp (Finset.mem_Iio.mp hv)
    have hw' : s ≤ (w : ℕ) := Fin.le_def.mp (Finset.mem_Ici.mp hw)
    show TuranMatching.Clique.bigClass k s v ≠ TuranMatching.Clique.bigClass k s w
    simp only [TuranMatching.Clique.bigClass, hv', if_true, not_lt.mpr hw', if_false]
    have : (v : ℕ) % (k - 1) < k - 1 := Nat.mod_lt _ (by omega)
    omega
  have hsub : ((A ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2))) ⊆
      (TuranMatching.Clique.bigGraph n k s).edgeFinset := by
    intro e he
    obtain ⟨⟨v, w⟩, hp, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at hp
    simpa using hcls v w hp.1 hp.2
  have hinj : Set.InjOn (fun p : Fin n × Fin n => s(p.1, p.2)) (A ×ˢ B : Finset _) := by
    intro p hp q hq h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
    have hp1 : (p.1 : ℕ) < s := Fin.lt_def.mp (Finset.mem_Iio.mp hp.1)
    have hp2 : s ≤ (p.2 : ℕ) := Fin.le_def.mp (Finset.mem_Ici.mp hp.2)
    have hq1 : (q.1 : ℕ) < s := Fin.lt_def.mp (Finset.mem_Iio.mp hq.1)
    have hq2 : s ≤ (q.2 : ℕ) := Fin.le_def.mp (Finset.mem_Ici.mp hq.2)
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso; have := congrArg Fin.val h1; omega
  calc s * (n - s) = #((A ×ˢ B).image (fun p : Fin n × Fin n => s(p.1, p.2))) := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_product, hA, hB]
    _ ≤ _ := Finset.card_le_card hsub

end TMCAux

theorem solution (n k s : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (hn : 3 * s ^ 2 + 2 * s < n) :
    (s - 1) * n + 2 * (s + 1) * s < TuranMatching.Clique.gNum n k s := by
  have hsn : s < n := by nlinarith
  have h := TMCAux.gNum_ge n k s hk hsn
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have e1 : (t + 1 - 1) = t := by omega
  obtain ⟨u, rfl⟩ : ∃ u, n = (t + 1) + u + 1 := ⟨n - (t + 1) - 1, by omega⟩
  have e2 : (t + 1 + u + 1 - (t + 1)) = u + 1 := by omega
  rw [e2] at h
  rw [e1]
  nlinarith
