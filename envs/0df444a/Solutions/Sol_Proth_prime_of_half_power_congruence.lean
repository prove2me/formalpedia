-- Prove2me | solution 1 for Proth.prime_of_half_power_congruence
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T23:24:54.256986+00:00
-- url     : https://prove2.me/submissions/fcefb5e4-f120-446d-a180-85bb7225d812

/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Copyright (c) 2025 Kenny Lau, Bhavik Mehta. All rights reserved.
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE files.

Pocklington and auxiliary lemmas adapted from PrimeCert at
ca5b4626afef3fe6a27834648f1b142edbe8d71e (PrimeCert/ForMathlib.lean and Pocklington.lean).
Proth specialization adapted from gersh/ternary-goldbach-lean at
27df23af6a712895f22204d0d81102baa74f0ebe
(Math/Problems/TernaryGoldbach/Certs/HelfgottPlattProthSoundness.lean).
Source mathematical criterion: Helfgott and Platt, arXiv:1305.3062v2, Theorem 2.3.
-/

/-
PrimeCert source headers specify Apache 2.0; the pinned revision's LICENSE is MIT.
Both notices are preserved for the adapted components.

MIT License

Copyright (c) 2026 Bhavik Mehta

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem Nat.modEq_finset_prod_iff {a b : ℕ} {ι : Type*} (s : Finset ι) (e : ι → ℕ)
    (co : (s : Set ι).Pairwise (Coprime.onFun e)) :
    a ≡ b [MOD ∏ i ∈ s, e i] ↔ ∀ i ∈ s, a ≡ b [MOD e i] := by
  classical
  obtain ⟨l, hl, rfl⟩ := s.exists_list_nodup_eq
  rw [List.prod_toFinset e hl, Nat.modEq_list_map_prod_iff]
  · simp_rw [List.mem_toFinset]
  · rwa [← List.pairwise_iff_coe_toFinset_pairwise hl]

theorem Nat.modEq_iff_forall_prime_dvd {a b n : ℕ} :
    a ≡ b [MOD n] ↔ ∀ p : ℕ, p ∣ n → p.Prime → a ≡ b [MOD p ^ multiplicity p n] := by
  by_cases hn₀ : n = 0
  · subst hn₀
    simp_rw [modEq_zero_iff, dvd_zero, true_imp_iff]
    constructor
    · rintro rfl; exact fun _ _ ↦ by rfl
    · intro h
      obtain ⟨p, hbp, hp⟩ := exists_infinite_primes (a + b + 1)
      specialize h p hp
      rw [multiplicity_zero, pow_one] at h
      exact h.eq_of_lt_of_lt (by linarith) (by linarith)
  · conv_lhs => rw [← prod_factorization_pow_eq_self hn₀]
    rw [Finsupp.prod, modEq_finset_prod_iff]
    · simp_rw [support_factorization, mem_primeFactors_of_ne_zero hn₀, and_comm, and_imp]
      refine forall_congr' fun p ↦ imp_congr_right fun hpn ↦ imp_congr_right fun hp ↦ ?_
      rw [multiplicity_eq_factorization hp hn₀]
    · grind [support_factorization, coprime_pow_primes, Set.Pairwise]

theorem Nat.pow_multiplicity_dvd_of_dvd_of_not_dvd_div
    {q n x : ℕ} (hq : q.Prime) (hxn : x ∣ n) (hxnq : ¬ x ∣ n / q) :
    q ^ multiplicity q n ∣ x := by
  by_cases hqn : q ∣ n
  · obtain ⟨n, rfl⟩ := hqn
    rw [Nat.mul_div_cancel_left _ hq.pos] at hxnq
    by_cases hn₀ : n = 0
    · subst hn₀; exact (hxnq <| dvd_zero _).elim
    have hqn₀ : q * n ≠ 0 := mul_ne_zero hq.ne_zero hn₀
    have hx₀ : x ≠ 0 := by rintro rfl; exact hqn₀ <| zero_dvd_iff.mp hxn
    rw [← Nat.factorization_le_iff_dvd hx₀ hn₀] at hxnq
    rw [← Nat.factorization_le_iff_dvd hx₀ hqn₀] at hxn
    rw [Nat.factorization_mul hq.ne_zero hn₀, hq.factorization, add_comm] at hxn
    refine pow_dvd_of_le_multiplicity ?_
    rw [multiplicity_eq_factorization hq hqn₀, multiplicity_eq_factorization hq hx₀,
      Nat.factorization_mul hq.ne_zero hn₀, Finsupp.add_apply, hq.factorization,
      Finsupp.single_apply, if_pos rfl, add_comm]
    refine le_of_not_gt fun h ↦ hxnq fun p ↦ ?_
    by_cases hpq : p = q
    · subst hpq; exact Nat.lt_succ_iff.mp h
    convert hxn p using 1
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hpq), add_zero]
  · rw [multiplicity_eq_zero.mpr hqn, pow_zero]
    exact one_dvd _


namespace GoldbachThree

/-- Let `N` be a natural number whose primality we want to certify.
Assume we have a partial factorisation `N - 1 = F₁ * R₁`, where `F₁` is fully factorised with
prime factors `pᵢ`.
Now for each `pᵢ` find a pseudo-primitive root `aᵢ` such that `aᵢ ^ (N - 1) ≡ 1 (mod N)` and
`gcd(aᵢ ^ ((N - 1) / pᵢ) - 1, N) = 1`.
Then any prime factor `n` of `N` satisfies `n ≡ 1 (mod F₁)`. -/
theorem pocklington_test (N F₁ : ℕ) (hn₀ : 0 < N) (hf₁ : F₁ ∣ N - 1)
    (primitive : ∀ p ∈ F₁.primeFactors, ∃ a : ℕ, a ^ (N - 1) ≡ 1 [MOD N] ∧
      Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1)
    (p : ℕ) (hp : p.Prime) (hpn : p ∣ N) : p ≡ 1 [MOD F₁] := by
  by_cases hn₁ : N = 1
  · rw [hn₁, Nat.dvd_one] at hpn
    exact absurd (hpn ▸ hp) Nat.not_prime_one
  -- `omega` is >2x faster than `lia` here (56ms vs 144ms median over 5 runs)
  replace hn₁ : 1 < N := by omega
  have hf₀ : F₁ ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hf₁
    omega
  rw [Nat.modEq_iff_forall_prime_dvd]
  intro q hqf hq
  have := Fact.mk hp
  have := (Nat.prime_iff_card_units _).mp hp
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hp.one_le, ← this]
  obtain ⟨a, han, hanq⟩ := primitive q (Nat.mem_primeFactors.mpr ⟨hq, hqf, hf₀⟩)
  have hanp := han.of_dvd hpn
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one] at hanp
  let a' : (ZMod p)ˣ := Units.ofPowEqOne _ _ hanp (by grind)
  refine dvd_trans ?_ (orderOf_dvd_card (x := a'))
  have : multiplicity q F₁ ≤ multiplicity q (N - 1) := by
    rw [Nat.multiplicity_eq_factorization hq hf₀, Nat.multiplicity_eq_factorization hq (by grind)]
    exact (Nat.factorization_le_iff_dvd hf₀ (by grind)).mpr hf₁ _
  refine dvd_trans (pow_dvd_pow _ this) ?_
  refine Nat.pow_multiplicity_dvd_of_dvd_of_not_dvd_div hq ?_ ?_
  · rwa [orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val]
  · rw [orderOf_dvd_iff_pow_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val]
    unfold a'
    have : 1 ≤ a ^ ((N - 1) / q) := Nat.one_le_pow _ _ <| pos_of_ne_zero fun ha₀ ↦ by
      subst ha₀; rw [Nat.cast_zero, zero_pow (by grind)] at hanp; simp at hanp
    rw [Units.val_ofPowEqOne, ← Nat.cast_pow, Units.val_one, ← Nat.cast_one (R := ZMod p),
      ZMod.natCast_eq_natCast_iff, Nat.ModEq.comm, Nat.modEq_iff_dvd' this,
      ← hp.coprime_iff_not_dvd]
    rw [← Nat.coprime_iff_gcd_eq_one] at hanq
    exact hanq.symm.coprime_dvd_left hpn

/-- The Pocklington primitive-root predicate: for each prime factor `p` of `F₁`,
`gcd(root ^ ((N-1)/p) - 1, N) = 1`. Built incrementally by `PocklingtonPred.step`. -/
def PocklingtonPred (N root F₁ : ℕ) : Prop :=
  ∀ p ∈ F₁.primeFactors, (root ^ ((N - 1) / p) - 1).gcd N = 1

theorem pocklington_certify (N F₁ : ℕ) (h2n : 2 ≤ N) (hf₁ : F₁ ∣ N - 1) (hf₁' : N.sqrt < F₁)
    (root : ℕ) (psp : root ^ (N - 1) ≡ 1 [MOD N])
    (primitive : PocklingtonPred N root F₁) :
    Nat.Prime N := by
  by_contra hn
  rw [Nat.sqrt_lt, ← sq] at hf₁'
  have := pocklington_test N F₁ (by grind) hf₁ (fun p hp ↦ ⟨root, psp, primitive p hp⟩)
    N.minFac (N.minFac_prime (by grind)) N.minFac_dvd
  have h1p : 2 ≤ N.minFac := (N.minFac_prime (by grind)).two_le
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' (by grind)] at this
  have := Nat.succ_le_iff.mp <| (Nat.le_sub_iff_add_le (by grind)).mp <|
    Nat.le_of_dvd (by grind) this
  exact lt_asymm hf₁' <| ((Nat.pow_lt_pow_iff_left (by grind)).mpr this).trans_le <|
    Nat.minFac_sq_le_self (by grind) hn


def prothN (n k : ℕ) : ℕ := k * 2 ^ n + 1

/-- Proth's primality criterion, in the one-way form needed by a certificate
checker. -/
theorem prime_of_proth_congruence (n k a : Nat)
    (hn : 1 ≤ n) (hk : 0 < k) (hkF : k < 2 ^ n)
    (hcong :
      a ^ ((prothN n k - 1) / 2) % prothN n k = prothN n k - 1) :
    Nat.Prime (prothN n k) := by
  let F : Nat := 2 ^ n
  let N : Nat := k * F + 1
  have hFpos : 0 < F := by simp [F]
  have hFtwo : 1 < F := by
    dsimp [F]
    exact one_lt_pow₀ (by omega) (by omega)
  have hkF' : k < F := by simpa [F] using hkF
  have hNtwo : 2 ≤ N := by simp [N, Nat.succ_le_iff, hk, hFpos]
  have htwoF : 2 ∣ F := by
    rcases n with _ | n
    · omega
    · simp [F, Nat.pow_succ]
  have hNm1 : N - 1 = k * F := by simp [N]
  have htwoNm1 : 2 ∣ N - 1 := by
    rw [hNm1]
    exact dvd_mul_of_dvd_right htwoF k
  have hhalf : (N - 1) / 2 * 2 = N - 1 := Nat.div_mul_cancel htwoNm1
  have hcong' : a ^ ((N - 1) / 2) % N = N - 1 := by
    simpa [N, F, prothN] using hcong
  apply pocklington_certify N F hNtwo
  · rw [hNm1]
    exact dvd_mul_left F k
  · rw [Nat.sqrt_lt]
    have hk1 : k + 1 ≤ F := Nat.succ_le_iff.mpr hkF'
    calc
      N = k * F + 1 := rfl
      _ < k * F + F := Nat.add_lt_add_left hFtwo (k * F)
      _ = (k + 1) * F := by ring
      _ ≤ F * F := Nat.mul_le_mul_right F hk1
  · rw [Nat.ModEq]
    rw [← hhalf, Nat.pow_mul, Nat.pow_two, Nat.mul_mod, hcong']
    have hNdecomp : N = (N - 2) + 2 := by omega
    have hNm1decomp : N - 1 = (N - 2) + 1 := by omega
    have hsq : (N - 1) * (N - 1) = N * (N - 2) + 1 := calc
      (N - 1) * (N - 1) = ((N - 2) + 1) * ((N - 2) + 1) := by
        rw [hNm1decomp]
      _ = ((N - 2) + 2) * (N - 2) + 1 := by ring
      _ = N * (N - 2) + 1 := by rw [← hNdecomp]
    rw [hsq]
    simp [Nat.add_mod]
  · intro p hp
    rw [Nat.primeFactors_prime_pow (by omega) Nat.prime_two] at hp
    simp only [Finset.mem_singleton] at hp
    subst p
    have hOddN : Odd N := by
      obtain ⟨d, hd⟩ := htwoF
      refine ⟨k * d, ?_⟩
      dsimp [N]
      rw [hd]
      ring
    have hcop : Nat.Coprime (N - 2) N :=
      (Nat.coprime_self_sub_left hNtwo).mpr
        (Nat.coprime_two_left.mpr hOddN)
    let x : Nat := a ^ ((N - 1) / 2)
    have hxmod : x % N = N - 1 := by simpa [x] using hcong'
    have hx : x = (N - 1) + N * (x / N) := by
      have h := Nat.mod_add_div x N
      rw [hxmod] at h
      omega
    have hxsub : x - 1 = (N - 2) + N * (x / N) := by omega
    rw [show a ^ ((N - 1) / 2) = x by rfl, hxsub]
    simpa [Nat.Coprime] using hcop


end GoldbachThree

theorem solution (n k a : ℕ) (hn : 1 ≤ n) (hk : 0 < k) (hkF : k < 2 ^ n)
    (hcong : a ^ ((k * 2 ^ n) / 2) % (k * 2 ^ n + 1) = k * 2 ^ n) :
    Nat.Prime (k * 2 ^ n + 1) := by
  apply GoldbachThree.prime_of_proth_congruence n k a hn hk hkF
  simpa only [GoldbachThree.prothN, Nat.add_sub_cancel] using hcong

#print axioms solution
