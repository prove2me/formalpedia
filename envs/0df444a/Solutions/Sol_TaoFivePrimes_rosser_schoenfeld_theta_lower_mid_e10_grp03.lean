-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp03
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:25:33.80584+00:00
-- url     : https://prove2.me/submissions/0597878f-7c52-45be-97a0-488f1c0ce648

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0101
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0102
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0103
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0104
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0105
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0106
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0107
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0108
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0109
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0110
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0111
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0112
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0113
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0114
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0115
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0116
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0117
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0118
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0119
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0120
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0121
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0122
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0123
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0124
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0125
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0126
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0127
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0128
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0129
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0130
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0131
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0132
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0133
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0134
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0135
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0136
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0137
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0138
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0139
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0140
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0141
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0142
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0143
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0144
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0145
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0146
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0147
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0148
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0149
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0150

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp03` (the range 1629291792 <= n <= 1948709899 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0101` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0150`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (1791373280619079820717 : Real) / 2 ^ 40 <= Chebyshev.theta (1629291792 : Real))
    (n : Nat) (h1 : 1629291792 <= n) (h2 : n <= 1948709899) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((2142555716222639034474 : Real) / 2 ^ 40 <= Chebyshev.theta (1948709900 : Real)) := by
  have hb0 := hbase
  have hb1 : (1798367222086236402867 : Real) / 2 ^ 40 <= Chebyshev.theta (1635643364 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0101 hb0 1629291792 le_rfl (by norm_num)).2
  have hb2 : (1805362444667358911321 : Real) / 2 ^ 40 <= Chebyshev.theta (1642002672 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0102 hb1 1635643364 le_rfl (by norm_num)).2
  have hb3 : (1812358945502251870851 : Real) / 2 ^ 40 <= Chebyshev.theta (1648373870 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0103 hb2 1642002672 le_rfl (by norm_num)).2
  have hb4 : (1819356720207403363626 : Real) / 2 ^ 40 <= Chebyshev.theta (1654748120 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0104 hb3 1648373870 le_rfl (by norm_num)).2
  have hb5 : (1826355764346644997740 : Real) / 2 ^ 40 <= Chebyshev.theta (1661114474 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0105 hb4 1654748120 le_rfl (by norm_num)).2
  have hb6 : (1833356072224890700738 : Real) / 2 ^ 40 <= Chebyshev.theta (1667478822 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0106 hb5 1661114474 le_rfl (by norm_num)).2
  have hb7 : (1840357638917922852797 : Real) / 2 ^ 40 <= Chebyshev.theta (1673850384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0107 hb6 1667478822 le_rfl (by norm_num)).2
  have hb8 : (1847360460308302885656 : Real) / 2 ^ 40 <= Chebyshev.theta (1680218414 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0108 hb7 1673850384 le_rfl (by norm_num)).2
  have hb9 : (1854364531341195353340 : Real) / 2 ^ 40 <= Chebyshev.theta (1686588930 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0109 hb8 1680218414 le_rfl (by norm_num)).2
  have hb10 : (1861369846577540007874 : Real) / 2 ^ 40 <= Chebyshev.theta (1692951368 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0110 hb9 1686588930 le_rfl (by norm_num)).2
  have hb11 : (1868376402906139312094 : Real) / 2 ^ 40 <= Chebyshev.theta (1699331832 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0111 hb10 1692951368 le_rfl (by norm_num)).2
  have hb12 : (1875384196458882172160 : Real) / 2 ^ 40 <= Chebyshev.theta (1705701510 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0112 hb11 1699331832 le_rfl (by norm_num)).2
  have hb13 : (1882393220805166466074 : Real) / 2 ^ 40 <= Chebyshev.theta (1712069664 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0113 hb12 1705701510 le_rfl (by norm_num)).2
  have hb14 : (1889403472781882443713 : Real) / 2 ^ 40 <= Chebyshev.theta (1718445854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0114 hb13 1712069664 le_rfl (by norm_num)).2
  have hb15 : (1896414947216415337231 : Real) / 2 ^ 40 <= Chebyshev.theta (1724819004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0115 hb14 1718445854 le_rfl (by norm_num)).2
  have hb16 : (1903427641168933731809 : Real) / 2 ^ 40 <= Chebyshev.theta (1731200898 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0116 hb15 1724819004 le_rfl (by norm_num)).2
  have hb17 : (1910441551226256141785 : Real) / 2 ^ 40 <= Chebyshev.theta (1737589170 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0117 hb16 1731200898 le_rfl (by norm_num)).2
  have hb18 : (1917456671950066580303 : Real) / 2 ^ 40 <= Chebyshev.theta (1743965558 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0118 hb17 1737589170 le_rfl (by norm_num)).2
  have hb19 : (1924472998858052466160 : Real) / 2 ^ 40 <= Chebyshev.theta (1750348988 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0119 hb18 1743965558 le_rfl (by norm_num)).2
  have hb20 : (1931490527666246806014 : Real) / 2 ^ 40 <= Chebyshev.theta (1756728852 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0120 hb19 1750348988 le_rfl (by norm_num)).2
  have hb21 : (1938509254380014116020 : Real) / 2 ^ 40 <= Chebyshev.theta (1763113700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0121 hb20 1756728852 le_rfl (by norm_num)).2
  have hb22 : (1945529174688035806762 : Real) / 2 ^ 40 <= Chebyshev.theta (1769497218 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0122 hb21 1763113700 le_rfl (by norm_num)).2
  have hb23 : (1952550285241322913978 : Real) / 2 ^ 40 <= Chebyshev.theta (1775889692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0123 hb22 1769497218 le_rfl (by norm_num)).2
  have hb24 : (1959572581212969958982 : Real) / 2 ^ 40 <= Chebyshev.theta (1782271278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0124 hb23 1775889692 le_rfl (by norm_num)).2
  have hb25 : (1966596058522007168278 : Real) / 2 ^ 40 <= Chebyshev.theta (1788658032 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0125 hb24 1782271278 le_rfl (by norm_num)).2
  have hb26 : (1973620713234270273832 : Real) / 2 ^ 40 <= Chebyshev.theta (1795041390 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0126 hb25 1788658032 le_rfl (by norm_num)).2
  have hb27 : (1980646539790314791885 : Real) / 2 ^ 40 <= Chebyshev.theta (1801425764 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0127 hb26 1795041390 le_rfl (by norm_num)).2
  have hb28 : (1987673535960148348601 : Real) / 2 ^ 40 <= Chebyshev.theta (1807817394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0128 hb27 1801425764 le_rfl (by norm_num)).2
  have hb29 : (1994701697871938544552 : Real) / 2 ^ 40 <= Chebyshev.theta (1814212704 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0129 hb28 1807817394 le_rfl (by norm_num)).2
  have hb30 : (2001731022243679916066 : Real) / 2 ^ 40 <= Chebyshev.theta (1820611410 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0130 hb29 1814212704 le_rfl (by norm_num)).2
  have hb31 : (2008761505299177617337 : Real) / 2 ^ 40 <= Chebyshev.theta (1827005682 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0131 hb30 1820611410 le_rfl (by norm_num)).2
  have hb32 : (2015793142359262001536 : Real) / 2 ^ 40 <= Chebyshev.theta (1833403380 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0132 hb31 1827005682 le_rfl (by norm_num)).2
  have hb33 : (2022825929115219393159 : Real) / 2 ^ 40 <= Chebyshev.theta (1839796070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0133 hb32 1833403380 le_rfl (by norm_num)).2
  have hb34 : (2029859862319280339949 : Real) / 2 ^ 40 <= Chebyshev.theta (1846193640 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0134 hb33 1839796070 le_rfl (by norm_num)).2
  have hb35 : (2036894938777076124841 : Real) / 2 ^ 40 <= Chebyshev.theta (1852596800 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0135 hb34 1846193640 le_rfl (by norm_num)).2
  have hb36 : (2043931154226409392185 : Real) / 2 ^ 40 <= Chebyshev.theta (1858994090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0136 hb35 1852596800 le_rfl (by norm_num)).2
  have hb37 : (2050968504842894388804 : Real) / 2 ^ 40 <= Chebyshev.theta (1865399832 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0137 hb36 1858994090 le_rfl (by norm_num)).2
  have hb38 : (2058006987654324341260 : Real) / 2 ^ 40 <= Chebyshev.theta (1871806968 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0138 hb37 1865399832 le_rfl (by norm_num)).2
  have hb39 : (2065046598313283995929 : Real) / 2 ^ 40 <= Chebyshev.theta (1878205542 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0139 hb38 1871806968 le_rfl (by norm_num)).2
  have hb40 : (2072087333080233367049 : Real) / 2 ^ 40 <= Chebyshev.theta (1884619050 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0140 hb39 1878205542 le_rfl (by norm_num)).2
  have hb41 : (2079129188988547639565 : Real) / 2 ^ 40 <= Chebyshev.theta (1891019168 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0141 hb40 1884619050 le_rfl (by norm_num)).2
  have hb42 : (2086172161148245205068 : Real) / 2 ^ 40 <= Chebyshev.theta (1897423458 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0142 hb41 1891019168 le_rfl (by norm_num)).2
  have hb43 : (2093216245636883908126 : Real) / 2 ^ 40 <= Chebyshev.theta (1903826490 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0143 hb42 1897423458 le_rfl (by norm_num)).2
  have hb44 : (2100261439739957387297 : Real) / 2 ^ 40 <= Chebyshev.theta (1910235530 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0144 hb43 1903826490 le_rfl (by norm_num)).2
  have hb45 : (2107307740309055049533 : Real) / 2 ^ 40 <= Chebyshev.theta (1916646032 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0145 hb44 1910235530 le_rfl (by norm_num)).2
  have hb46 : (2114355144186835168373 : Real) / 2 ^ 40 <= Chebyshev.theta (1923064700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0146 hb45 1916646032 le_rfl (by norm_num)).2
  have hb47 : (2121403647624268428806 : Real) / 2 ^ 40 <= Chebyshev.theta (1929475128 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0147 hb46 1923064700 le_rfl (by norm_num)).2
  have hb48 : (2128453246085827579715 : Real) / 2 ^ 40 <= Chebyshev.theta (1935881238 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0148 hb47 1929475128 le_rfl (by norm_num)).2
  have hb49 : (2135503936716713038975 : Real) / 2 ^ 40 <= Chebyshev.theta (1942297544 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0149 hb48 1935881238 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0150 hb49 1942297544 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 1788658032 with hc25 | hc25
  · rcases Nat.lt_or_ge n 1705701510 with hc12 | hc12
    · rcases Nat.lt_or_ge n 1667478822 with hc6 | hc6
      · rcases Nat.lt_or_ge n 1648373870 with hc3 | hc3
        · rcases Nat.lt_or_ge n 1635643364 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0101 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1642002672 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0102 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0103 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1654748120 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0104 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1661114474 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0105 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0106 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1686588930 with hc9 | hc9
        · rcases Nat.lt_or_ge n 1673850384 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0107 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1680218414 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0108 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0109 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1692951368 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0110 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1699331832 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0111 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0112 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 1743965558 with hc18 | hc18
      · rcases Nat.lt_or_ge n 1724819004 with hc15 | hc15
        · rcases Nat.lt_or_ge n 1712069664 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0113 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1718445854 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0114 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0115 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1731200898 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0116 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1737589170 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0117 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0118 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1763113700 with hc21 | hc21
        · rcases Nat.lt_or_ge n 1750348988 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0119 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1756728852 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0120 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0121 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1775889692 with hc23 | hc23
          · rcases Nat.lt_or_ge n 1769497218 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0122 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0123 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1782271278 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0124 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0125 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 1865399832 with hc37 | hc37
    · rcases Nat.lt_or_ge n 1827005682 with hc31 | hc31
      · rcases Nat.lt_or_ge n 1807817394 with hc28 | hc28
        · rcases Nat.lt_or_ge n 1795041390 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0126 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1801425764 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0127 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0128 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1814212704 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0129 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1820611410 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0130 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0131 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1846193640 with hc34 | hc34
        · rcases Nat.lt_or_ge n 1833403380 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0132 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1839796070 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0133 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0134 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1852596800 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0135 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1858994090 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0136 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0137 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 1903826490 with hc43 | hc43
      · rcases Nat.lt_or_ge n 1884619050 with hc40 | hc40
        · rcases Nat.lt_or_ge n 1871806968 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0138 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1878205542 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0139 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0140 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1891019168 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0141 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1897423458 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0142 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0143 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 1923064700 with hc46 | hc46
        · rcases Nat.lt_or_ge n 1910235530 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0144 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1916646032 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0145 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0146 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1935881238 with hc48 | hc48
          · rcases Nat.lt_or_ge n 1929475128 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0147 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0148 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1942297544 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0149 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0150 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (1791373280619079820717 : Real) / 2 ^ 40 <= Chebyshev.theta (1629291792 : Real))
    (n : Nat) (h1 : 1629291792 <= n) (h2 : n <= 1948709899) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((2142555716222639034474 : Real) / 2 ^ 40 <= Chebyshev.theta (1948709900 : Real)) :=
  TFPLink.blk hbase n h1 h2
